import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.State

/-! # Checks.Cases.Fs.Stat — what `readlinkat`, `newfstatat` and `fstat` answer, read off against Linux

Worked examples over `Sys.Fs.Stat.readlinkat_spec`, `newfstatat_spec` and
`fstat_spec`, the twin of `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`.
Not part of the trusted specification: this file is QA on the definitions,
written to be READ, and every claim in it is a claim about what the kernel
does, with the citation beside it.  Line numbers are Linux v6.18.46 (commit
1f99e9ab748f).

HOW THESE ARE STATED.  A check is stated on the relation itself, as an
`iff` over EVERY outcome `o`, so one theorem fixes what is admitted and what
is refused; beside it, the concrete lie a kernel could tell is refuted on
its own.  Where an arm answers one outcome the `iff` has a single right-hand
side; where `fstat` delivers a `struct stat` the admitted set is infinite
and the `iff` names the three conditions the spec puts on the bytes —
`stat_buf_wf`, the size implication, and agreement with the pin — so that
the concrete admissions and refusals follow from it.  Every proof is
`sys_norm` or `sys_refute` (`Checks/Cases/Tactic.lean`), or an `iff`
rewritten in followed by a witness and `decide`, or `rfl` on a closed
reading; the few that are not say why where they occur.

WHAT THE ROCQ FILE PINS AND WHAT IT PROBES.  Rocq's `Checks/Cases/Fs/Stat.v`
keeps the copy-in ledger example for `newfstatat` and its examples over the
bytes `fstat` delivers, and sends the rest — every errno arm, the
truncation, the kinds that decline — to probes against a real kernel
(`testing/syscall-check/tests/fstat_spec.c`, `newfstatat_spec.c`,
`readlinkat_dirfd.c` and `errno_readlinkat.c`).  This file pins every arm
in Lean: the Rocq examples as twins (`rocq-twin:`); each probed arm on the
case that recorded it (`probe:`) where the pin's registers — descriptor
numbers, flag words, sizes — are the probe's; and otherwise on the kernel
functions that decide it (`kernel:`), with the probe's case named in
prose, so a reader can go from a pin to the kernel run it stands on.

NOT PORTED: Rocq's `fstat_model_rw`, `fstat_read_write_fd_answers_as_a_file`
and `fstat_read_write_wrong_size_rejected`: `fstat_spec` declines
`FdFileRW` (`Sys/Fs/Stat.lean`'s header) where Rocq answers through
`fstat_file_spec`, so there is no answer for the two to state;
`a17_rdwr_fstat_declines` below holds the decline, and the three land
with the port of that arm.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins prove
is that this spec and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Stat

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Stat
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.State (pin_run read_cstr_aux_run)

/-! ## The register

The specs' unfoldings, at low priority like every other (the
`Checks/Cases/Tactic.lean` header says why), and `record_copyins`, the
wrapper `newfstatat_spec` is spelled with; nothing for the gates, which
are decided, never unfolded.  The call fixtures below enter by their
unfoldings, so a projection of one reduces to the memory map it names;
the model fixtures stay opaque behind projection lemmas. -/

attribute [sys_simp low]
  readlinkat_spec.eq_1 newfstatat_spec.eq_1 newfstatat_core_spec.eq_1
  fstat_spec.eq_1 fstat_file_spec.eq_1 fstat_chrdev_spec.eq_1 fstat_devnull_spec.eq_1
  fstat_urandom_spec.eq_1
/- `record_copyins` is `Sys/Syscall.lean`'s wrapper, shared by every copy-in
spec and not in `Checks/Cases/Tactic.lean`'s register; it is registered
LOCALLY here (as `Checks/Cases/Kernel/Sched/Syscalls.lean` registers it for
itself) so that two leaf files do not both edit the shared set.  The one
registration in `Tactic.lean` is a `lean: base:` change. -/
attribute [local sys_simp low] record_copyins.eq_1

/-! ## newfstatat: the pathnames, the calls and the processes

`statat_absent_model` is Rocq's: the demo process over an EMPTY file
system.  `statat_exists_model` holds one byte in "f".  The pathname
memories lay a string out at 0x2000 and nothing else, through
`Prelude.bytes_at`; `path_toolong` is 4096 non-NUL bytes and a NUL, from
`Checks/Cases/State.lean`'s `pin_run`, the shape whose 4096-step walk the
kernel cannot evaluate and that file reads in closed form instead. -/

/-- "f" and its NUL at 0x2000. -/
def path_f : word → Option byte := bytes_at 0x2000 [102, 0]
/-- The empty pathname: a NUL at 0x2000. -/
def path_empty : word → Option byte := bytes_at 0x2000 [0]
/-- "." and its NUL at 0x2000. -/
def path_dot : word → Option byte := bytes_at 0x2000 [46, 0]
/-- ".." and its NUL at 0x2000. -/
def path_dotdot : word → Option byte := bytes_at 0x2000 [46, 46, 0]
/-- "f/x" and its NUL at 0x2000. -/
def path_fx : word → Option byte := bytes_at 0x2000 [102, 47, 120, 0]
/-- "f" at 0x2000 with 0x2001 unmapped: the NUL faults. -/
def path_runoff : word → Option byte := bytes_at 0x2000 [102]
/-- Nothing readable at all: the pointer faults on its first byte. -/
def path_none : word → Option byte := fun _ => none
/-- 4096 bytes of 'a' from 0x2000 and then a NUL, one past PATH_MAX.
IRREDUCIBLE on purpose: the walk over it is 4096 steps deep, which neither
the elaborator's `whnf` nor the kernel can take (`Checks/Cases/State.lean`'s
PATH_MAX pins say the same), so nothing may evaluate it; the two closed-form
readings below are the only way through. -/
@[irreducible] def path_toolong : word → Option byte := pin_run 0x2000 4096

/-- Syscall 79 with the given dirfd and flag registers, the pathname at
0x2000, `statbuf` NULL, over the given readable memory. -/
def statat_call (dirfd flag : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 79 [dirfd, 0x2000, 0, flag, 0, 0] mem (fun _ => none)

/-- Rocq's `statat_absent_input` generalised over the memory: AT_FDCWD,
the pathname at 0x2000, flag 0. -/
def statat_input (mem : word → Option byte) : SyscallInput := statat_call AT_FDCWD 0 mem

/-- Syscall 79 with a NULL pathname pointer and nothing readable. -/
def statat_null_input : SyscallInput :=
  SyscallInput.mkInput 79 [AT_FDCWD, 0, 0, 0, 0, 0] path_none (fun _ => none)

attribute [sys_simp low] statat_call.eq_1 statat_input.eq_1 statat_null_input.eq_1

/-! ### The dispatcher's argument reads

`in_arg` is not in `sys_simp`, so a spec reached through the table would
keep `in_arg (mkInput …) k` stuck until the ground pass and leave the
match on the pathname unresolved in pass 1.  The three positions the
specs here read, on any six-register call, closed by `rfl`. -/

/-- model: the dispatcher's first register on a literal call, a rewrite for `sys_norm`. -/
theorem in_arg_0 (n a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 0 = a0 := rfl
/-- model: the dispatcher's second register on a literal call, a rewrite for `sys_norm`. -/
theorem in_arg_1 (n a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 1 = a1 := rfl
/-- model: the dispatcher's fourth register on a literal call, a rewrite for `sys_norm`. -/
theorem in_arg_3 (n a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 3 = a3 := rfl

/- LOCAL: `Checks/Cases/Kernel/Sched/Syscalls.lean` states the same three
readings for its own pins; the one copy both files want is a `lean: base:`
line in `Checks/Cases/Tactic.lean` beside `bind_arg_iff`, and until it
lands neither file should widen the shared set. -/
attribute [local sys_simp] in_arg_0 in_arg_1 in_arg_3

/-- Rocq's `statat_absent_model`: the demo process, empty file system. -/
def statat_absent_model : Model := fixture_of
/-- The same process holding one byte in "f". -/
def statat_exists_model : Model := fixture_of (fs := [([102], [120])])

/-! ### The fixtures' readings -/

/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_statat_absent_model : m_fs statat_absent_model = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_statat_exists_model : m_fs statat_exists_model = [([102], [120])] := rfl
/-- The same reading in the form the normalizer leaves once `m_fs` has
unfolded on the bound model (the `Checks/Cases/Tactic.lean` header:
children are simplified before their parent, so the getter opens on `m`
before `bind_get_model_iff` substitutes the fixture).
model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_statat_absent_model : statat_absent_model.m_fsys.fsst_image = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_statat_exists_model : statat_exists_model.m_fsys.fsst_image = [([102], [120])] := rfl
/-- model: a closed `fs_lookup` in the fixture map, a rewrite for `sys_norm`. -/
theorem fs_lookup_absent_f : Fs.fs_lookup [] [102] = none := rfl
/-- model: a closed `fs_lookup` in the fixture map, a rewrite for `sys_norm`. -/
theorem fs_lookup_exists_f : Fs.fs_lookup [([102], [120])] [102] = some [120] := rfl

/-- "f" reads as the one-byte string.
model: a closed `read_cstr` over a fixture memory, a rewrite for `sys_norm`. -/
theorem read_cstr_path_f : read_cstr path_f 0x2000 = CstrOk [102] := by decide
/-- …and the fetch that read it is two bytes, the NUL included.
model: a closed `cstr_access_len_aux` over a fixture memory, a rewrite for `sys_norm`. -/
theorem len_path_f : cstr_access_len_aux path_f 0x2000 path_max = 2 := by decide
/-- The empty pathname reads as the empty string.
model: a closed `read_cstr` over a fixture memory, a rewrite for `sys_norm`. -/
theorem read_cstr_path_empty : read_cstr path_empty 0x2000 = CstrOk [] := by decide
/-- …fetched as its one NUL byte.
model: a closed `cstr_access_len_aux` over a fixture memory, a rewrite for `sys_norm`. -/
theorem len_path_empty : cstr_access_len_aux path_empty 0x2000 path_max = 1 := by decide
/-- "." reads as the dot path.
model: a closed `read_cstr` over a fixture memory, a rewrite for `sys_norm`. -/
theorem read_cstr_path_dot : read_cstr path_dot 0x2000 = CstrOk [46] := by decide
/-- …fetched as two bytes.
model: a closed `cstr_access_len_aux` over a fixture memory, a rewrite for `sys_norm`. -/
theorem len_path_dot : cstr_access_len_aux path_dot 0x2000 path_max = 2 := by decide
/-- ".." reads as two dots.
model: a closed `read_cstr` over a fixture memory, a rewrite for `sys_norm`. -/
theorem read_cstr_path_dotdot : read_cstr path_dotdot 0x2000 = CstrOk [46, 46] := by decide
/-- …fetched as three bytes.
model: a closed `cstr_access_len_aux` over a fixture memory, a rewrite for `sys_norm`. -/
theorem len_path_dotdot : cstr_access_len_aux path_dotdot 0x2000 path_max = 3 := by decide
/-- "f/x" reads as its three bytes.
model: a closed `read_cstr` over a fixture memory, a rewrite for `sys_norm`. -/
theorem read_cstr_path_fx : read_cstr path_fx 0x2000 = CstrOk [102, 47, 120] := by decide
/-- …fetched as four bytes.
model: a closed `cstr_access_len_aux` over a fixture memory, a rewrite for `sys_norm`. -/
theorem len_path_fx : cstr_access_len_aux path_fx 0x2000 path_max = 4 := by decide
/-- The flat map holds no "f/x" beside "f".
model: a closed `fs_lookup` in the fixture map, a rewrite for `sys_norm`. -/
theorem fs_lookup_exists_fx : Fs.fs_lookup [([102], [120])] [102, 47, 120] = none := by decide
/-- A string whose NUL is unmapped faults.
model: a closed `read_cstr` over a fixture memory, a rewrite for `sys_norm`. -/
theorem read_cstr_path_runoff : read_cstr path_runoff 0x2000 = CstrFault := by decide
/-- …and the fetch counts the faulting byte: two.
model: a closed `cstr_access_len_aux` over a fixture memory, a rewrite for `sys_norm`. -/
theorem len_path_runoff : cstr_access_len_aux path_runoff 0x2000 path_max = 2 := by decide
/-- A NULL pointer faults on its first byte.
model: a closed `read_cstr` over a fixture memory, a rewrite for `sys_norm`. -/
theorem read_cstr_path_none_0 : read_cstr path_none 0 = CstrFault := by decide
/-- …and that one attempted byte is the whole ledger.
model: a closed `cstr_access_len_aux` over a fixture memory, a rewrite for `sys_norm`. -/
theorem len_path_none_0 : cstr_access_len_aux path_none 0 path_max = 1 := by decide
/-- An unmapped pathname pointer at 0x2000 faults the same way.
model: a closed `read_cstr` over a fixture memory, a rewrite for `sys_norm`. -/
theorem read_cstr_path_none_0x2000 : read_cstr path_none 0x2000 = CstrFault := by decide
/-- model: a closed `cstr_access_len_aux` over a fixture memory, a rewrite for `sys_norm`. -/
theorem len_path_none_0x2000 : cstr_access_len_aux path_none 0x2000 path_max = 1 := by decide

/-- 4096 content bytes have no NUL within PATH_MAX: too long.  Read in
closed form through `Checks/Cases/State.lean`'s `read_cstr_aux_run`,
since a 4096-step evaluation is outside the kernel's budget.
model: a closed `read_cstr` over a fixture memory, a rewrite for `sys_norm`. -/
theorem read_cstr_path_toolong : read_cstr path_toolong 0x2000 = CstrTooLong := by
  unfold path_toolong
  exact (read_cstr_aux_run 0x2000 4096 (by decide) 4096 0 (Nat.zero_le 4096)).trans (by decide)

/-- `pin_run` read through `cstr_access_len_aux`, in closed form: from
offset `i` of the run the fetch counts the remaining `n - i` content
bytes and the NUL, capped by the fuel.  The companion of
`Checks/Cases/State.lean`'s `read_cstr_aux_run`, for the ledger's side of
the same walk.
model: `cstr_access_len_aux` over `pin_run`, a closed form for the PATH_MAX ledger. -/
theorem cstr_access_len_aux_run (lo n : Nat) (hn : lo + n < 2 ^ 64) (k : Nat) :
    ∀ i, i ≤ n →
      cstr_access_len_aux (pin_run lo n) (BitVec.ofNat 64 (lo + i)) k = min k (n - i + 1) := by
  induction k with
  | zero =>
    intro i _
    simp only [cstr_access_len_aux, Nat.zero_min]
  | succ k ih =>
    intro i hi
    have hto : (BitVec.ofNat 64 (lo + i)).toNat = lo + i := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hstep : BitVec.ofNat 64 (lo + i) + 1 = BitVec.ofNat 64 (lo + (i + 1)) := by
      rw [← Nat.add_assoc, BitVec.ofNat_add (lo + i) 1]
      rfl
    have hlo : lo ≤ lo + i := Nat.le_add_right lo i
    simp only [cstr_access_len_aux, pin_run, hto, hlo, ↓reduceIte]
    by_cases hlt : lo + i < lo + n
    · have hne : bv_eqb 0x61#8 (Z_to_bv 8 0) = false := by decide
      simp only [hlt, ↓reduceIte, hne, Bool.false_eq_true, hstep]
      rw [ih (i + 1) (by omega)]
      omega
    · have hi' : i = n := by omega
      subst hi'
      have hz : bv_eqb 0#8 (Z_to_bv 8 0) = true := by decide
      simp only [hlt, ↓reduceIte, hz]
      omega

/-- The PATH_MAX fetch charges exactly PATH_MAX bytes: `strncpy_from_user`
was asked for that many and stopped there.
model: a closed `cstr_access_len_aux` over a fixture memory, a rewrite for `sys_norm`. -/
theorem len_path_toolong : cstr_access_len_aux path_toolong 0x2000 path_max = 4096 := by
  unfold path_toolong
  exact (cstr_access_len_aux_run 0x2000 4096 (by decide) 4096 0 (Nat.zero_le 4096)).trans (by decide)

attribute [sys_simp]
  m_fs_statat_absent_model m_fs_statat_exists_model fs_statat_absent_model fs_statat_exists_model
  fs_lookup_absent_f fs_lookup_exists_f
  read_cstr_path_f len_path_f read_cstr_path_empty len_path_empty read_cstr_path_dot len_path_dot
  read_cstr_path_dotdot len_path_dotdot read_cstr_path_fx len_path_fx fs_lookup_exists_fx
  read_cstr_path_runoff len_path_runoff read_cstr_path_none_0 len_path_none_0
  read_cstr_path_none_0x2000 len_path_none_0x2000 read_cstr_path_toolong len_path_toolong

/-! ## fstat: the files, the landing zones and the delivered struct

Rocq's fixtures name for name: "f", nine bytes long — a length no
neighbouring member of the struct coincides with, so a rejection at
`st_size` cannot be one at `st_blocks` or `st_nlink` read through a wrong
offset — held through fd 3 read-only over a table that holds fd 3 alone; a
128-byte writable landing zone at 4096 and the same zone one byte shy; and
`stat_of`, a `struct stat` in the asm-generic layout written member by
member at the offsets `Uapi` names, whose five arguments are what the
examples vary.  Everything else in it is a plausible constant and none of
it is claimed to be what any kernel would report. -/

def fstat_path : Fs.path := [102]
def fstat_data : List byte := List.replicate 9 65
def fstat_data_grown : List byte := List.replicate 12 65

/-- fd 3 alone, on "f", as Rocq's `with_fds` leaves the table. -/
def fstat_fds : List (word × FdEntry) := [(3, .FdFile fstat_path 0)]

def fstat_model_of (d : List byte) : Model := fixture_of (fds := fstat_fds) (fs := [(fstat_path, d)])
def fstat_model : Model := fstat_model_of fstat_data
def fstat_model_grown : Model := fstat_model_of fstat_data_grown

/-- A descriptor on a path the map does not hold: what `unlinkat` leaves. -/
def fstat_model_unlinked : Model := fixture_of (fds := fstat_fds)

/-- A 128-byte writable landing zone at 4096. -/
def stat_out : word → Option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4224 then some 0 else none
/-- …and the same zone one byte shy: what separates `copy_to_user`'s
-EFAULT from the decline a partial copy gets. -/
def stat_out_short : word → Option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4223 then some 0 else none

/-- Syscall 80 on the given fd and `statbuf` registers over the given
writable memory; the readable view is empty, since `fstat` reads no user
byte. -/
def fstat_call (fd statbuf : word) (wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 80 [fd, statbuf, 0, 0, 0, 0] (fun _ => none) wmem

/-- Rocq's `fstat_input`: fd 3, `statbuf` 4096, the full landing zone. -/
def fstat_input : SyscallInput := fstat_call 3 4096 stat_out
/-- The same call over the zone one byte shy. -/
def fstat_input_short : SyscallInput := fstat_call 3 4096 stat_out_short

attribute [sys_simp low] fstat_call.eq_1 fstat_input.eq_1 fstat_input_short.eq_1

/-- A `struct stat` in the asm-generic layout riscv64 inherits
(include/uapi/asm-generic/stat.h:24-45, v6.18.46), written member by member: an
ext4-ish `st_dev`, the given inode, mode, one link, the demo user, no
`st_rdev`, zero `__pad1`, the given size, a 4096-byte block size, zero
`__pad2`, the given block count, the given seconds in all three
timestamps with zero nanoseconds, and zero `__unused4`/`__unused5`.
IRREDUCIBLE, as every struct fixture below is: a predicate over 128 bytes
is more than the elaborator's `whnf` takes in one breath, so no proof may
evaluate one; each value a pin needs is a closed fact below, decided by
the kernel (`decide +kernel`) and registered as a rewrite. -/
@[irreducible] def stat_of (ino mode size blocks tim : Int) : List byte :=
  Z_to_le_bytes 8 2049 ++ Z_to_le_bytes 8 ino ++ Z_to_le_bytes 4 mode ++ Z_to_le_bytes 4 1
  ++ Z_to_le_bytes 4 1000 ++ Z_to_le_bytes 4 1000 ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 0
  ++ Z_to_le_bytes 8 size ++ Z_to_le_bytes 4 4096 ++ Z_to_le_bytes 4 0 ++ Z_to_le_bytes 8 blocks
  ++ Z_to_le_bytes 8 tim ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 tim ++ Z_to_le_bytes 8 0
  ++ Z_to_le_bytes 8 tim ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 0

/-- The truthful answer for the nine-byte file: a regular file of length
nine, inode 4711.  Nothing but the width, the padding, the type's validity
and the length is checked, so every other member here is free. -/
@[irreducible] def stat_truthful : List byte := stat_of 4711 S_IFREG 9 8 1700000000
/-- S_IFCHR with `st_size` 0: the true answer for a path Linux calls a
character device. -/
@[irreducible] def stat_ifchr_zero : List byte := stat_of 4711 S_IFCHR 0 0 1700000000
/-- Eight bytes under S_IFREG where the map holds nine. -/
@[irreducible] def stat_short_size : List byte := stat_of 4711 S_IFREG 8 8 1700000000
/-- Twelve bytes under S_IFREG, with a later timestamp: the answer after a
write of three bytes. -/
@[irreducible] def stat_grown : List byte := stat_of 4711 S_IFREG 12 8 1700000042
/-- The truthful struct with one nonzero byte in `__pad1` (bytes 40..47). -/
@[irreducible] def stat_pad1_poisoned : List byte :=
  stat_truthful.take 40 ++ Z_to_le_bytes 8 1 ++ stat_truthful.drop 48
/-- The truthful struct with one nonzero byte in `__unused4`/`__unused5`
(bytes 120..127). -/
@[irreducible] def stat_unused45_poisoned : List byte := stat_truthful.take 120 ++ Z_to_le_bytes 8 1
/-- The truthful struct with one nonzero byte in `__pad2` (bytes 60..63). -/
@[irreducible] def stat_pad2_poisoned : List byte :=
  stat_truthful.take 60 ++ Z_to_le_bytes 4 1 ++ stat_truthful.drop 64
/-- 128 zero bytes: the shape a kernel that wrote nothing and said it did
would produce. -/
@[irreducible] def zero_stat : List byte := List.replicate 128 0
/-- `st_mode` = `S_IFMT`, every type bit set: none of the seven types. -/
@[irreducible] def stat_ifmt_type : List byte := stat_of 4711 S_IFMT 9 8 1700000000
/-- The truthful struct with inode 4712 instead: the defector against a
pin, and an admissible first answer. -/
@[irreducible] def stat_other_inode : List byte := stat_of 4712 S_IFREG 9 8 1700000000
/-- The truthful struct with new timestamps and a new block count: the
members the pin does not hold. -/
@[irreducible] def stat_new_times : List byte := stat_of 4711 S_IFREG 9 16 1700000099
/-- The truthful struct with `st_blksize` 512 instead of 4096 (bytes
56..59): the defector in the pin's third slice, which nothing but
`stat_stable_eqb` constrains. -/
@[irreducible] def stat_other_blksize : List byte :=
  stat_truthful.take 56 ++ Z_to_le_bytes 4 512 ++ stat_truthful.drop 60
/-- The truthful struct's first 127 bytes. -/
@[irreducible] def stat_short127 : List byte := stat_truthful.take 127
/-- The truthful struct and eight more bytes: 136. -/
@[irreducible] def stat_long136 : List byte := stat_truthful ++ Z_to_le_bytes 8 0

/-- The same layout for a character device node on devtmpfs: device 5,
root's, the given inode, mode, `st_rdev`, size and block count. -/
@[irreducible] def chrdev_stat_of (ino mode rdev size blocks tim : Int) : List byte :=
  Z_to_le_bytes 8 5 ++ Z_to_le_bytes 8 ino ++ Z_to_le_bytes 4 mode ++ Z_to_le_bytes 4 1
  ++ Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 0 ++ Z_to_le_bytes 8 rdev ++ Z_to_le_bytes 8 0
  ++ Z_to_le_bytes 8 size ++ Z_to_le_bytes 4 4096 ++ Z_to_le_bytes 4 0 ++ Z_to_le_bytes 8 blocks
  ++ Z_to_le_bytes 8 tim ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 tim ++ Z_to_le_bytes 8 0
  ++ Z_to_le_bytes 8 tim ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 0

/-- The truthful answer for /dev/null: S_IFCHR, `st_rdev` 259 (1:3), zero
size and blocks, inode 17. -/
@[irreducible] def devnull_truthful : List byte := chrdev_stat_of 17 S_IFCHR 259 0 0 1700000000
/-- /dev/null's truthful struct cut to 100 bytes: every member
`stat_devnull_ok` reads is there, and the width is wrong. -/
@[irreducible] def devnull_short100 : List byte := devnull_truthful.take 100
/-- The null device reported as a REGULAR file. -/
@[irreducible] def devnull_as_regular : List byte := chrdev_stat_of 17 S_IFREG 259 0 0 1700000000
/-- The null device with `st_rdev` 0. -/
@[irreducible] def devnull_zero_rdev : List byte := chrdev_stat_of 17 S_IFCHR 0 0 0 1700000000
/-- The null device with a nonzero `st_size`. -/
@[irreducible] def devnull_sized : List byte := chrdev_stat_of 17 S_IFCHR 259 5 0 1700000000
/-- The null device with a nonzero `st_blocks`. -/
@[irreducible] def devnull_blocks : List byte := chrdev_stat_of 17 S_IFCHR 259 0 8 1700000000
/-- The null device's truthful struct with new timestamps. -/
@[irreducible] def devnull_new_times : List byte := chrdev_stat_of 17 S_IFCHR 259 0 0 1700000099
/-- The null device's truthful struct with inode 18 instead. -/
@[irreducible] def devnull_other_inode : List byte := chrdev_stat_of 18 S_IFCHR 259 0 0 1700000000
/-- The truthful answer for /dev/urandom: S_IFCHR, `st_rdev` 265 (1:9),
zero size and blocks, inode 23. -/
@[irreducible] def urandom_truthful : List byte := chrdev_stat_of 23 S_IFCHR 265 0 0 1700000000
/-- The random device reported as a REGULAR file. -/
@[irreducible] def urandom_as_regular : List byte := chrdev_stat_of 23 S_IFREG 265 0 0 1700000000
/-- The random device with a nonzero `st_size`. -/
@[irreducible] def urandom_sized : List byte := chrdev_stat_of 23 S_IFCHR 265 5 0 1700000000
/-- The random device with a nonzero `st_blocks`. -/
@[irreducible] def urandom_blocks : List byte := chrdev_stat_of 23 S_IFCHR 265 0 8 1700000000
/-- The random device's truthful struct with new timestamps. -/
@[irreducible] def urandom_new_times : List byte := chrdev_stat_of 23 S_IFCHR 265 0 0 1700000099
/-- The random device's truthful struct with inode 24 instead. -/
@[irreducible] def urandom_other_inode : List byte := chrdev_stat_of 24 S_IFCHR 265 0 0 1700000000

/-! ### What the predicates say of each struct

Every value a pin depends on, decided by the kernel once and registered as
a rewrite, so the normalizer reads a predicate off a struct the way it reads
a lookup off a table: without evaluating it.  Each is a claim about the
`Uapi` predicates on a fixture, not about Linux; the pins that use them
carry the kernel claim. -/

/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_truthful : stat_buf_wf stat_truthful = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_ifchr_zero : stat_buf_wf stat_ifchr_zero = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_short_size : stat_buf_wf stat_short_size = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_grown : stat_buf_wf stat_grown = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_pad1_poisoned : stat_buf_wf stat_pad1_poisoned = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_unused45_poisoned : stat_buf_wf stat_unused45_poisoned = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_pad2_poisoned : stat_buf_wf stat_pad2_poisoned = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_other_blksize : stat_buf_wf stat_other_blksize = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_zero_stat : stat_buf_wf zero_stat = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_ifmt_type : stat_buf_wf stat_ifmt_type = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_other_inode : stat_buf_wf stat_other_inode = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_new_times : stat_buf_wf stat_new_times = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_short127 : stat_buf_wf stat_short127 = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_long136 : stat_buf_wf stat_long136 = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_devnull : stat_buf_wf devnull_truthful = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_devnull_short100 : stat_buf_wf devnull_short100 = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_devnull_as_regular : stat_buf_wf devnull_as_regular = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_devnull_zero_rdev : stat_buf_wf devnull_zero_rdev = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_devnull_sized : stat_buf_wf devnull_sized = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_devnull_new_times : stat_buf_wf devnull_new_times = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_devnull_other_inode : stat_buf_wf devnull_other_inode = true := by decide +kernel

/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem size9_truthful : stat_size_ok 9 stat_truthful = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem size12_truthful : stat_size_ok 12 stat_truthful = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem size0_truthful : stat_size_ok 0 stat_truthful = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem size9_ifchr_zero : stat_size_ok 9 stat_ifchr_zero = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem size9_short_size : stat_size_ok 9 stat_short_size = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem size12_grown : stat_size_ok 12 stat_grown = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem size9_other_inode : stat_size_ok 9 stat_other_inode = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem size9_new_times : stat_size_ok 9 stat_new_times = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem size9_other_blksize : stat_size_ok 9 stat_other_blksize = true := by decide +kernel

/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem stable_truthful : stat_stable_eqb stat_truthful stat_truthful = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem stable_grown : stat_stable_eqb stat_grown stat_truthful = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem stable_other_inode : stat_stable_eqb stat_other_inode stat_truthful = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem stable_new_times : stat_stable_eqb stat_new_times stat_truthful = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem stable_other_blksize : stat_stable_eqb stat_other_blksize stat_truthful = false := by
  decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem stable_devnull : stat_stable_eqb devnull_truthful devnull_truthful = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem stable_devnull_new_times : stat_stable_eqb devnull_new_times devnull_truthful = true := by
  decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem stable_devnull_other_inode : stat_stable_eqb devnull_other_inode devnull_truthful = false := by
  decide +kernel

/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_devnull : stat_devnull_ok devnull_truthful = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_devnull_short100 : stat_devnull_ok devnull_short100 = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_devnull_as_regular : stat_devnull_ok devnull_as_regular = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_devnull_zero_rdev : stat_devnull_ok devnull_zero_rdev = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_devnull_sized : stat_devnull_ok devnull_sized = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_devnull_blocks : stat_buf_wf devnull_blocks = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_devnull_blocks : stat_devnull_ok devnull_blocks = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_devnull_new_times : stat_devnull_ok devnull_new_times = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_devnull_other_inode : stat_devnull_ok devnull_other_inode = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_truthful : stat_devnull_ok stat_truthful = false := by decide +kernel

/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_urandom : stat_buf_wf urandom_truthful = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_urandom_as_regular : stat_buf_wf urandom_as_regular = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_urandom_sized : stat_buf_wf urandom_sized = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_urandom_new_times : stat_buf_wf urandom_new_times = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_urandom_other_inode : stat_buf_wf urandom_other_inode = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem stable_urandom_new_times : stat_stable_eqb urandom_new_times urandom_truthful = true := by
  decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem stable_urandom_other_inode : stat_stable_eqb urandom_other_inode urandom_truthful = false := by
  decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_urandom : stat_urandom_ok urandom_truthful = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_urandom_as_regular : stat_urandom_ok urandom_as_regular = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_urandom_sized : stat_urandom_ok urandom_sized = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem wf_urandom_blocks : stat_buf_wf urandom_blocks = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_urandom_blocks : stat_urandom_ok urandom_blocks = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_urandom_new_times : stat_urandom_ok urandom_new_times = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_urandom_other_inode : stat_urandom_ok urandom_other_inode = true := by decide +kernel
/-- The two devices the model knows differ in `st_rdev` alone, and each
predicate refuses the other's record.
model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_urandom_of_devnull_record : stat_urandom_ok devnull_truthful = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `sys_norm`. -/
theorem ok_devnull_of_urandom_record : stat_devnull_ok urandom_truthful = false := by decide +kernel

attribute [sys_simp]
  wf_truthful wf_ifchr_zero wf_short_size wf_grown wf_pad1_poisoned wf_unused45_poisoned wf_zero_stat
  wf_ifmt_type wf_other_inode wf_new_times wf_short127 wf_long136 wf_devnull wf_devnull_short100
  wf_devnull_as_regular wf_devnull_zero_rdev wf_devnull_sized wf_devnull_new_times wf_devnull_other_inode
  size9_truthful size12_truthful size0_truthful size9_ifchr_zero size9_short_size size12_grown
  size9_other_inode size9_new_times
  stable_truthful stable_grown stable_other_inode stable_new_times stable_devnull
  stable_devnull_new_times stable_devnull_other_inode
  ok_devnull ok_devnull_short100 ok_devnull_as_regular ok_devnull_zero_rdev ok_devnull_sized
  ok_devnull_new_times ok_devnull_other_inode ok_truthful
  wf_urandom wf_urandom_as_regular wf_urandom_sized wf_urandom_new_times wf_urandom_other_inode
  stable_urandom_new_times stable_urandom_other_inode
  ok_urandom ok_urandom_as_regular ok_urandom_sized ok_urandom_new_times ok_urandom_other_inode
  ok_urandom_of_devnull_record ok_devnull_of_urandom_record
  wf_pad2_poisoned wf_other_blksize size9_other_blksize stable_other_blksize
  wf_devnull_blocks ok_devnull_blocks wf_urandom_blocks ok_urandom_blocks

/-- Rocq's `with_statpin fstat_path stat_truthful fstat_model`: the file
already statted once, its identity recorded. -/
def fstat_model_pinned : Model := with_statpin fstat_path stat_truthful fstat_model
/-- The pinned file after it grew to twelve bytes. -/
def fstat_model_grown_pinned : Model := with_statpin fstat_path stat_truthful fstat_model_grown
/-- The pinned file unlinked and recreated at the same name: what
`with_fs [] ` and then `with_fs [(f, data)]` leave — the pin gone. -/
def fstat_model_recreated : Model := with_fs [(fstat_path, fstat_data)] (with_fs [] fstat_model_pinned)

/-- fd 3 the nine-byte "f" and fd 4 an EMPTY "g": the probe's two-files
shape, where the kernel's nine bytes are wrong about fd 4. -/
def fstat_two_fds : List (word × FdEntry) := [(3, .FdFile fstat_path 0), (4, .FdFile [103] 0)]
def fstat_two_files_model : Model :=
  fixture_of (fds := fstat_two_fds) (fs := [(fstat_path, fstat_data), ([103], [])])
/-- …with "f" already statted once and "g" not. -/
def fstat_two_files_model_pinned_f : Model :=
  with_statpin fstat_path stat_truthful fstat_two_files_model

/-- Every descriptor kind Rocq's table never needed: a channel at 0, the
file at 3 read-only and at 9 for writing, /dev/null at 4, a directory at
5, a fresh socket at 6, a pipe's read end at 7 and /dev/urandom at 8. -/
def fstat_kinds_fds : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (3, .FdFile fstat_path 0), (4, .FdDevNull true true), (5, .FdDir),
    (6, .FdSocket .SkFresh), (7, .FdPipe 0 false), (8, .FdUrandom), (9, .FdFileW fstat_path 0) ]
def fstat_kinds_model : Model :=
  fixture_of (fds := fstat_kinds_fds) (pipes := [(0, ([], 0))]) (fs := [(fstat_path, fstat_data)])
/-- …with /dev/null already statted once. -/
def fstat_kinds_model_pinned : Model := with_statpin devnull_path devnull_truthful fstat_kinds_model
/-- …with /dev/urandom already statted once. -/
def fstat_kinds_model_urandom_pinned : Model :=
  with_statpin urandom_path urandom_truthful fstat_kinds_model

/-! Three records NO RUN BUILDS, for the receptiveness guards: the only
writer of a pin is the branch that has just checked the predicate, so a
pin failing it exists in no reachable model.  The guards are pinned all
the same, because receptiveness is a statement about every `Model`, and
because a spec that dropped the guard would hand the `choose` below it an
empty set — the one shape `Monad` forbids — with nothing else to notice. -/

/-- "f" pinned under an all-zero record: 128 bytes that name no file type,
so not `stat_buf_wf`. -/
def fstat_model_badpin : Model := with_statpin fstat_path zero_stat fstat_model
/-- /dev/null pinned under a REGULAR FILE's record: well-formed, and not
`stat_devnull_ok`. -/
def fstat_kinds_model_badpin_file : Model := with_statpin devnull_path stat_truthful fstat_kinds_model
/-- /dev/null pinned under a 100-byte prefix of its truthful record: every
member `stat_devnull_ok` reads is there and agrees, and the width is not
128, so not `stat_buf_wf`. -/
def fstat_kinds_model_badpin_short : Model :=
  with_statpin devnull_path devnull_short100 fstat_kinds_model
/-- /dev/urandom pinned under the NULL DEVICE's record: well-formed, a
character device, and not `stat_urandom_ok` — `st_rdev` is 259, not 265. -/
def fstat_kinds_model_urandom_badpin_devnull : Model :=
  with_statpin urandom_path devnull_truthful fstat_kinds_model

/-! ### The fixtures' readings

Each model stays a name in the normal form behind its projections, and
each lookup the pins need is one closed fact, all `rfl`.  The two
`read_bytes_map` facts are what separates the landing zone from the zone
one byte shy. -/

/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_model : m_fds fstat_model = fstat_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_model : m_fs fstat_model = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_statpins_fstat_model : m_statpins fstat_model = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_model_grown : m_fds fstat_model_grown = fstat_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_model_grown : m_fs fstat_model_grown = [(fstat_path, fstat_data_grown)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_statpins_fstat_model_grown : m_statpins fstat_model_grown = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_model_unlinked : m_fds fstat_model_unlinked = fstat_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_model_unlinked : m_fs fstat_model_unlinked = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_model_pinned : m_fds fstat_model_pinned = fstat_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_model_pinned : m_fs fstat_model_pinned = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_statpins_fstat_model_pinned :
    m_statpins fstat_model_pinned = [(fstat_path, stat_truthful)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_model_grown_pinned : m_fds fstat_model_grown_pinned = fstat_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_model_grown_pinned :
    m_fs fstat_model_grown_pinned = [(fstat_path, fstat_data_grown)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_statpins_fstat_model_grown_pinned :
    m_statpins fstat_model_grown_pinned = [(fstat_path, stat_truthful)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_model_recreated : m_fds fstat_model_recreated = fstat_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_model_recreated : m_fs fstat_model_recreated = [(fstat_path, fstat_data)] := rfl
/-- The recreated file carries NO pin: `with_fs []` dropped it.
model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_statpins_fstat_model_recreated : m_statpins fstat_model_recreated = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_two_files_model : m_fds fstat_two_files_model = fstat_two_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_two_files_model :
    m_fs fstat_two_files_model = [(fstat_path, fstat_data), ([103], [])] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_statpins_fstat_two_files_model : m_statpins fstat_two_files_model = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_two_files_model_pinned_f : m_fds fstat_two_files_model_pinned_f = fstat_two_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_two_files_model_pinned_f :
    m_fs fstat_two_files_model_pinned_f = [(fstat_path, fstat_data), ([103], [])] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_statpins_fstat_two_files_model_pinned_f :
    m_statpins fstat_two_files_model_pinned_f = [(fstat_path, stat_truthful)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_kinds_model : m_fds fstat_kinds_model = fstat_kinds_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_kinds_model : m_fs fstat_kinds_model = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_statpins_fstat_kinds_model : m_statpins fstat_kinds_model = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_kinds_model_pinned : m_fds fstat_kinds_model_pinned = fstat_kinds_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_kinds_model_pinned :
    m_fs fstat_kinds_model_pinned = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_statpins_fstat_kinds_model_pinned :
    m_statpins fstat_kinds_model_pinned = [(devnull_path, devnull_truthful)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_model_badpin : m_fds fstat_model_badpin = fstat_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_model_badpin : m_fs fstat_model_badpin = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_statpins_fstat_model_badpin :
    m_statpins fstat_model_badpin = [(fstat_path, zero_stat)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_kinds_model_badpin_file : m_fds fstat_kinds_model_badpin_file = fstat_kinds_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_kinds_model_badpin_file :
    m_fs fstat_kinds_model_badpin_file = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_statpins_fstat_kinds_model_badpin_file :
    m_statpins fstat_kinds_model_badpin_file = [(devnull_path, stat_truthful)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_kinds_model_badpin_short :
    m_fds fstat_kinds_model_badpin_short = fstat_kinds_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_kinds_model_badpin_short :
    m_fs fstat_kinds_model_badpin_short = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_statpins_fstat_kinds_model_badpin_short :
    m_statpins fstat_kinds_model_badpin_short = [(devnull_path, devnull_short100)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_kinds_model_urandom_pinned :
    m_fds fstat_kinds_model_urandom_pinned = fstat_kinds_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_kinds_model_urandom_pinned :
    m_fs fstat_kinds_model_urandom_pinned = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_statpins_fstat_kinds_model_urandom_pinned :
    m_statpins fstat_kinds_model_urandom_pinned = [(urandom_path, urandom_truthful)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fds_fstat_kinds_model_urandom_badpin_devnull :
    m_fds fstat_kinds_model_urandom_badpin_devnull = fstat_kinds_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_fs_fstat_kinds_model_urandom_badpin_devnull :
    m_fs fstat_kinds_model_urandom_badpin_devnull = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem m_statpins_fstat_kinds_model_urandom_badpin_devnull :
    m_statpins fstat_kinds_model_urandom_badpin_devnull = [(urandom_path, devnull_truthful)] := rfl

/-! The same readings in the form the normalizer leaves once the getters
have unfolded on the bound model (the `Checks/Cases/Tactic.lean` header:
children are simplified before their parent, so `m_fds m` opens to
`m.m_fd.fdst_table` before `bind_get_model_iff` substitutes the fixture),
so the fd table, the file system and the pins are read in pass 1 and the
fixture itself stays a name. -/
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_model : fstat_model.m_fd.fdst_table = fstat_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_model : fstat_model.m_fsys.fsst_image = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_model : fstat_model.m_proc.procst_statpins = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_model_grown : fstat_model_grown.m_fd.fdst_table = fstat_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_model_grown : fstat_model_grown.m_fsys.fsst_image = [(fstat_path, fstat_data_grown)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_model_grown : fstat_model_grown.m_proc.procst_statpins = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_model_unlinked : fstat_model_unlinked.m_fd.fdst_table = fstat_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_model_unlinked : fstat_model_unlinked.m_fsys.fsst_image = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_model_unlinked : fstat_model_unlinked.m_proc.procst_statpins = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_model_pinned : fstat_model_pinned.m_fd.fdst_table = fstat_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_model_pinned : fstat_model_pinned.m_fsys.fsst_image = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_model_pinned : fstat_model_pinned.m_proc.procst_statpins = [(fstat_path, stat_truthful)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_model_grown_pinned : fstat_model_grown_pinned.m_fd.fdst_table = fstat_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_model_grown_pinned : fstat_model_grown_pinned.m_fsys.fsst_image = [(fstat_path, fstat_data_grown)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_model_grown_pinned : fstat_model_grown_pinned.m_proc.procst_statpins = [(fstat_path, stat_truthful)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_model_recreated : fstat_model_recreated.m_fd.fdst_table = fstat_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_model_recreated : fstat_model_recreated.m_fsys.fsst_image = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_model_recreated : fstat_model_recreated.m_proc.procst_statpins = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_two_files_model : fstat_two_files_model.m_fd.fdst_table = fstat_two_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_two_files_model : fstat_two_files_model.m_fsys.fsst_image = [(fstat_path, fstat_data), ([103], [])] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_two_files_model : fstat_two_files_model.m_proc.procst_statpins = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_two_files_model_pinned_f : fstat_two_files_model_pinned_f.m_fd.fdst_table = fstat_two_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_two_files_model_pinned_f : fstat_two_files_model_pinned_f.m_fsys.fsst_image = [(fstat_path, fstat_data), ([103], [])] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_two_files_model_pinned_f : fstat_two_files_model_pinned_f.m_proc.procst_statpins = [(fstat_path, stat_truthful)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_kinds_model : fstat_kinds_model.m_fd.fdst_table = fstat_kinds_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_kinds_model : fstat_kinds_model.m_fsys.fsst_image = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_kinds_model : fstat_kinds_model.m_proc.procst_statpins = [] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_kinds_model_pinned : fstat_kinds_model_pinned.m_fd.fdst_table = fstat_kinds_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_kinds_model_pinned : fstat_kinds_model_pinned.m_fsys.fsst_image = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_kinds_model_pinned : fstat_kinds_model_pinned.m_proc.procst_statpins = [(devnull_path, devnull_truthful)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_model_badpin : fstat_model_badpin.m_fd.fdst_table = fstat_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_model_badpin : fstat_model_badpin.m_fsys.fsst_image = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_model_badpin : fstat_model_badpin.m_proc.procst_statpins = [(fstat_path, zero_stat)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_kinds_model_badpin_file : fstat_kinds_model_badpin_file.m_fd.fdst_table = fstat_kinds_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_kinds_model_badpin_file : fstat_kinds_model_badpin_file.m_fsys.fsst_image = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_kinds_model_badpin_file : fstat_kinds_model_badpin_file.m_proc.procst_statpins = [(devnull_path, stat_truthful)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_kinds_model_badpin_short : fstat_kinds_model_badpin_short.m_fd.fdst_table = fstat_kinds_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_kinds_model_badpin_short : fstat_kinds_model_badpin_short.m_fsys.fsst_image = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_kinds_model_badpin_short : fstat_kinds_model_badpin_short.m_proc.procst_statpins = [(devnull_path, devnull_short100)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_kinds_model_urandom_pinned : fstat_kinds_model_urandom_pinned.m_fd.fdst_table = fstat_kinds_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_kinds_model_urandom_pinned : fstat_kinds_model_urandom_pinned.m_fsys.fsst_image = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_kinds_model_urandom_pinned : fstat_kinds_model_urandom_pinned.m_proc.procst_statpins = [(urandom_path, urandom_truthful)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fds_fstat_kinds_model_urandom_badpin_devnull : fstat_kinds_model_urandom_badpin_devnull.m_fd.fdst_table = fstat_kinds_fds := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem fs_fstat_kinds_model_urandom_badpin_devnull : fstat_kinds_model_urandom_badpin_devnull.m_fsys.fsst_image = [(fstat_path, fstat_data)] := rfl
/-- model: a fixture projection, a rewrite for `sys_norm`. -/
theorem pins_fstat_kinds_model_urandom_badpin_devnull : fstat_kinds_model_urandom_badpin_devnull.m_proc.procst_statpins = [(urandom_path, devnull_truthful)] := rfl

/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_fstat_3 : fd_lookup fstat_fds 3 = some (.FdFile fstat_path 0) := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_fstat_9 : fd_lookup fstat_fds 9 = none := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_fstat_12345 : fd_lookup fstat_fds 12345 = none := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_fstat_ffffffff : fd_lookup fstat_fds 4294967295 = none := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_two_3 : fd_lookup fstat_two_fds 3 = some (.FdFile fstat_path 0) := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_two_4 : fd_lookup fstat_two_fds 4 = some (.FdFile [103] 0) := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_0 : fd_lookup fstat_kinds_fds 0 = some (.FdChannel 0) := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_3 : fd_lookup fstat_kinds_fds 3 = some (.FdFile fstat_path 0) := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_4 : fd_lookup fstat_kinds_fds 4 = some (.FdDevNull true true) := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_5 : fd_lookup fstat_kinds_fds 5 = some .FdDir := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_6 : fd_lookup fstat_kinds_fds 6 = some (.FdSocket .SkFresh) := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_7 : fd_lookup fstat_kinds_fds 7 = some (.FdPipe 0 false) := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_8 : fd_lookup fstat_kinds_fds 8 = some .FdUrandom := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_9 : fd_lookup fstat_kinds_fds 9 = some (.FdFileW fstat_path 0) := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_kinds_10 : fd_lookup fstat_kinds_fds 10 = none := rfl

/-- model: a closed `fs_lookup` in the fixture map, a rewrite for `sys_norm`. -/
theorem fs_lookup_fstat : Fs.fs_lookup [(fstat_path, fstat_data)] fstat_path = some fstat_data := rfl
/-- model: a closed `fs_lookup` in the fixture map, a rewrite for `sys_norm`. -/
theorem fs_lookup_fstat_grown :
    Fs.fs_lookup [(fstat_path, fstat_data_grown)] fstat_path = some fstat_data_grown := rfl
/-- model: a closed `fs_lookup` in the fixture map, a rewrite for `sys_norm`. -/
theorem fs_lookup_fstat_unlinked : Fs.fs_lookup [] fstat_path = none := rfl
/-- model: a closed `fs_lookup` in the fixture map, a rewrite for `sys_norm`. -/
theorem fs_lookup_two_f :
    Fs.fs_lookup [(fstat_path, fstat_data), ([103], [])] fstat_path = some fstat_data := rfl
/-- model: a closed `fs_lookup` in the fixture map, a rewrite for `sys_norm`. -/
theorem fs_lookup_two_g : Fs.fs_lookup [(fstat_path, fstat_data), ([103], [])] [103] = some [] := rfl
/-! `List.length_nil` joins the register too, LOCALLY: the empty file's
`data.length` must read as the `0` the size facts are stated on, and a core
lemma the normalizer wants belongs in `Checks/Cases/Tactic.lean`, not in a
leaf file's contribution to the shared set. -/
attribute [local sys_simp] List.length_nil

/-- model: the fixture file's length, a rewrite for `sys_norm`. -/
theorem fstat_data_length : fstat_data.length = 9 := rfl
/-- model: the grown fixture file's length, a rewrite for `sys_norm`. -/
theorem fstat_data_grown_length : fstat_data_grown.length = 12 := rfl

/-- The landing zone backs all 128 bytes.
model: a closed `read_bytes_map` over a fixture memory, a rewrite for `sys_norm`. -/
theorem stat_out_reads :
    read_bytes_map stat_out 4096 (Z_to_bv 64 STAT_SIZE) = some (List.replicate 128 0) := by decide
/-- The zone one byte shy does not.
model: a closed `read_bytes_map` over a fixture memory, a rewrite for `sys_norm`. -/
theorem stat_out_short_faults :
    read_bytes_map stat_out_short 4096 (Z_to_bv 64 STAT_SIZE) = none := by decide
/-- The zone at the very top of the address space `access_ok` still admits
(`TASK_SIZE - 128`) is not backed by the fixture memory.
model: a closed `read_bytes_map` over a fixture memory, a rewrite for `sys_norm`. -/
theorem stat_out_top_faults :
    read_bytes_map stat_out (Z_to_bv 64 (2 ^ 47 - 128)) (Z_to_bv 64 STAT_SIZE) = none := by decide

attribute [sys_simp]
  m_fds_fstat_model m_fs_fstat_model m_statpins_fstat_model
  m_fds_fstat_model_grown m_fs_fstat_model_grown m_statpins_fstat_model_grown
  m_fds_fstat_model_unlinked m_fs_fstat_model_unlinked
  m_fds_fstat_model_pinned m_fs_fstat_model_pinned m_statpins_fstat_model_pinned
  m_fds_fstat_model_grown_pinned m_fs_fstat_model_grown_pinned m_statpins_fstat_model_grown_pinned
  m_fds_fstat_model_recreated m_fs_fstat_model_recreated m_statpins_fstat_model_recreated
  m_fds_fstat_two_files_model m_fs_fstat_two_files_model m_statpins_fstat_two_files_model
  m_fds_fstat_two_files_model_pinned_f m_fs_fstat_two_files_model_pinned_f
  m_statpins_fstat_two_files_model_pinned_f
  fds_fstat_two_files_model_pinned_f fs_fstat_two_files_model_pinned_f
  pins_fstat_two_files_model_pinned_f
  m_fds_fstat_kinds_model m_fs_fstat_kinds_model m_statpins_fstat_kinds_model
  m_fds_fstat_kinds_model_pinned m_fs_fstat_kinds_model_pinned m_statpins_fstat_kinds_model_pinned
  m_fds_fstat_model_badpin m_fs_fstat_model_badpin m_statpins_fstat_model_badpin
  m_fds_fstat_kinds_model_badpin_file m_fs_fstat_kinds_model_badpin_file
  m_statpins_fstat_kinds_model_badpin_file
  m_fds_fstat_kinds_model_badpin_short m_fs_fstat_kinds_model_badpin_short
  m_statpins_fstat_kinds_model_badpin_short
  fds_fstat_model fs_fstat_model pins_fstat_model fds_fstat_model_grown fs_fstat_model_grown
  pins_fstat_model_grown fds_fstat_model_unlinked fs_fstat_model_unlinked pins_fstat_model_unlinked
  fds_fstat_model_pinned fs_fstat_model_pinned pins_fstat_model_pinned fds_fstat_model_grown_pinned
  fs_fstat_model_grown_pinned pins_fstat_model_grown_pinned fds_fstat_model_recreated
  fs_fstat_model_recreated pins_fstat_model_recreated fds_fstat_two_files_model
  fs_fstat_two_files_model pins_fstat_two_files_model fds_fstat_kinds_model fs_fstat_kinds_model
  pins_fstat_kinds_model fds_fstat_kinds_model_pinned fs_fstat_kinds_model_pinned
  pins_fstat_kinds_model_pinned fds_fstat_model_badpin fs_fstat_model_badpin
  pins_fstat_model_badpin fds_fstat_kinds_model_badpin_file fs_fstat_kinds_model_badpin_file
  pins_fstat_kinds_model_badpin_file fds_fstat_kinds_model_badpin_short
  fs_fstat_kinds_model_badpin_short pins_fstat_kinds_model_badpin_short
  m_fds_fstat_kinds_model_urandom_pinned m_fs_fstat_kinds_model_urandom_pinned
  m_statpins_fstat_kinds_model_urandom_pinned
  m_fds_fstat_kinds_model_urandom_badpin_devnull m_fs_fstat_kinds_model_urandom_badpin_devnull
  m_statpins_fstat_kinds_model_urandom_badpin_devnull
  fds_fstat_kinds_model_urandom_pinned fs_fstat_kinds_model_urandom_pinned
  pins_fstat_kinds_model_urandom_pinned
  fds_fstat_kinds_model_urandom_badpin_devnull fs_fstat_kinds_model_urandom_badpin_devnull
  pins_fstat_kinds_model_urandom_badpin_devnull
  lookup_fstat_3 lookup_fstat_9 lookup_fstat_12345 lookup_fstat_ffffffff lookup_two_3 lookup_two_4
  lookup_kinds_0 lookup_kinds_3 lookup_kinds_4 lookup_kinds_5 lookup_kinds_6 lookup_kinds_7
  lookup_kinds_8 lookup_kinds_9 lookup_kinds_10
  fs_lookup_fstat fs_lookup_fstat_grown fs_lookup_fstat_unlinked fs_lookup_two_f fs_lookup_two_g
  fstat_data_length fstat_data_grown_length stat_out_reads stat_out_short_faults stat_out_top_faults

/-! ## readlinkat (78): `do_readlinkat`, and the dirfd it resolves first

`SYSCALL_DEFINE4(readlinkat, …)` (fs/stat.c:604-608, v6.18.46) is `do_readlinkat`
(:563-602), which fetches the name (:575), resolves it through
`filename_lookup` (:576) — where `path_init` (fs/namei.c:2540-2645) takes
the working directory for AT_FDCWD (:2590-2604) and answers -EBADF for a
descriptor the process does not hold (:2607-2611) — and then, for a
resolved path that is not a symlink and has no `->readlink`, answers
-EINVAL (fs/stat.c:585-594, v6.18.46).  The spec reads the dirfd alone, so under
AT_FDCWD every call is that -EINVAL: Linux's answer for a name that
resolves to a non-symlink, and the FALSE REJECTION
bugs/readlinkat-path-not-interpreted.md records for a name that does not
resolve (Linux: -ENOENT) or a pointer that cannot be read (-EFAULT).  The
two are pinned apart below.  Under any other dirfd the answer depends on
a directory the model cannot name, and the spec declines.  Nothing in
the spec reads the model, so the pins over a symbolic `m` hold on every
model; the concrete ones fix the input to the probe's shape. -/

/-- The 64-byte buffer at 0x3000 the probes hand `readlinkat`, zeroed. -/
def readlink_out : word → Option byte := bytes_at 0x3000 (List.replicate 64 0)

/-- Syscall 78 with `dirfd`, the pathname at 0x2000, the buffer at 0x3000
and the given `bufsiz`, over the given readable memory: the probes' shape
(`readlinkat_dirfd.c` passes `sizeof buf` = 64, `errno_readlinkat.c` 16). -/
def readlinkat_call (dirfd bufsiz : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 78 [dirfd, 0x2000, 0x3000, bufsiz, 0, 0] mem readlink_out

attribute [sys_simp low] readlinkat_call.eq_1

/-- THE SPEC'S ANSWER UNDER AT_FDCWD, for every input and model: -EINVAL
and nothing else, because the pathname is not read.  Where the name
resolves to a non-symlink this is `do_readlinkat`'s own `else` arm
(fs/stat.c:585-594, v6.18.46), the regular file the next pin fixes; where
it does not, Linux answers -ENOENT, or -EFAULT, or -ENOENT for the empty
name (:593), and this arm rejects a conforming trace — the recorded
divergence `readlinkat_missing_path_is_einval_here` pins by name.
kernel: fs/stat.c:readlinkat,do_readlinkat; fs/namei.c:path_init@v6.18.46 -/
theorem readlinkat_at_fdcwd_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    readlinkat_spec (fd32 AT_FDCWD) i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- A REGULAR FILE the model holds, named through AT_FDCWD: -EINVAL, the
probe's `ok` case (readlink of a regular file).
probe: testing/syscall-check/tests/readlinkat_dirfd.c#conform -- ok -/
theorem readlinkat_regular_file_is_einval (o : outcome SyscallEffect) :
    readlinkat_spec (fd32 AT_FDCWD) (readlinkat_call AT_FDCWD 64 path_f) statat_exists_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) statat_exists_model [] := by
  sys_norm

/-- A kernel reporting a zero-length symlink target has resolved a
symlink where the model has none.
probe: testing/syscall-check/tests/readlinkat_dirfd.c#reject --mutate readlinkat:ret=0 -- ok -/
theorem readlinkat_success_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ readlinkat_spec (fd32 AT_FDCWD) i m (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- Nor is it -ENOENT on the regular file: `do_readlinkat` answers -ENOENT
for a name the walk cannot resolve or for the EMPTY name (fs/stat.c:593,
v6.18.46), and this one resolves.
probe: testing/syscall-check/tests/readlinkat_dirfd.c#reject --mutate readlinkat:ret=-ENOENT -- ok -/
theorem readlinkat_enoent_rejected (m' : Model) (evs : List event) :
    ¬ readlinkat_spec (fd32 AT_FDCWD) (readlinkat_call AT_FDCWD 64 path_f) statat_exists_model
        (Ok (mkEffect (errno_ret ENOENT) [] []) m' evs) := by
  sys_refute

/-- Nor -EBADF: AT_FDCWD is never looked up in the fd table
(`path_init`, fs/namei.c:2590, v6.18.46).
probe: testing/syscall-check/tests/errno_readlinkat.c#reject --mutate readlinkat:ret=-EBADF -- readlinkat -/
theorem readlinkat_ebadf_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ readlinkat_spec (fd32 AT_FDCWD) i m (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- THE RECORDED FALSE REJECTION, stated as what it is.  A name the file
system does not hold is -ENOENT on Linux — the walk's own answer
(`walk_component`, fs/namei.c:2134-2158, v6.18.46, through `step_into`,
:1984-2022), which the probe's `missing` case records as a `reject` —
and this spec answers -EINVAL for it all the same: the coarsening
bugs/readlinkat-path-not-interpreted.md carries, admitted by the probe
only under the mutation that makes the kernel say the model's answer.
probe: testing/syscall-check/tests/readlinkat_dirfd.c#conform --mutate readlinkat:ret=-EINVAL -- missing -/
theorem readlinkat_missing_path_is_einval_here (o : outcome SyscallEffect) :
    readlinkat_spec (fd32 AT_FDCWD) (readlinkat_call AT_FDCWD 64 path_f) statat_absent_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) statat_absent_model [] := by
  sys_norm

/-- …so Linux's own -ENOENT for the missing name is REFUSED: the trace the
probe's `missing` case rejects, kept visible rather than argued away.
probe: testing/syscall-check/tests/readlinkat_dirfd.c#reject -- missing -/
theorem readlinkat_missing_path_enoent_refused (m' : Model) (evs : List event) :
    ¬ readlinkat_spec (fd32 AT_FDCWD) (readlinkat_call AT_FDCWD 64 path_f) statat_absent_model
        (Ok (mkEffect (errno_ret ENOENT) [] []) m' evs) := by
  sys_refute

/-- Any other dirfd is declined, fail closed.  A COVERAGE GAP, not an
empty intersection: Linux answers -EBADF for a closed descriptor
(`path_init`, fs/namei.c:2610-2611, v6.18.46), -ENOTDIR for a live one that is not
a directory (:2621-2622), and walks from a live directory — three answers
the model would have to pick between from a table it does not consult
here, and asserting -EINVAL would reject the first two.
probe: testing/syscall-check/tests/readlinkat_dirfd.c#fail-closed -- bad-dirfd -/
theorem readlinkat_other_dirfd_is_unmodeled (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    readlinkat_spec 999 i m o ↔ o = Unmodeled := by
  sys_norm

/-- …so the model's own -EINVAL is refused there: offered on a dirfd the
process does not hold, where Linux says -EBADF, it is not admitted.
probe: testing/syscall-check/tests/readlinkat_dirfd.c#fail-closed --mutate readlinkat:ret=-EINVAL -- bad-dirfd -/
theorem readlinkat_other_dirfd_einval_rejected (i : SyscallInput) (m m' : Model)
    (evs : List event) :
    ¬ readlinkat_spec 999 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A LIVE descriptor that is not a directory is declined too: the spec
reads the number alone, and Linux's -ENOTDIR (`path_init`,
fs/namei.c:2621-2622, v6.18.46) is one of the answers it does not pick between.
probe: testing/syscall-check/tests/readlinkat_dirfd.c#fail-closed -- live-dirfd -/
theorem readlinkat_live_dirfd_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    readlinkat_spec 3 i fstat_model o ↔ o = Unmodeled := by
  sys_norm

/-! ### The dispatcher: syscall 78 and the `int dfd` truncation

`__NR_readlinkat` is 78 (include/uapi/asm-generic/unistd.h:206-207, v6.18.46;
`78 common readlinkat sys_readlinkat` in the table riscv generates,
scripts/syscall.tbl:100).  `dfd` is `int` in the `SYSCALL_DEFINE4`
(fs/stat.c:604-605), narrowed by `__SYSCALL_DEFINEx`
(arch/riscv/include/asm/syscall_wrapper.h:82-88, v6.18.46) through `__SC_CAST`
(include/linux/syscalls.h:132), so only the low half of the register is
compared with AT_FDCWD. -/

/-- Syscall 78 with AT_FDCWD in a0, on a regular file the model holds,
reaches the arm and answers -EINVAL (the probe's call: `readlinkat(AT_FDCWD,
"ef", buf, 16)` on a file it created).
probe: testing/syscall-check/tests/errno_readlinkat.c#conform -- readlinkat -/
theorem sysno_78_is_readlinkat (o : outcome SyscallEffect) :
    syscall_spec (readlinkat_call AT_FDCWD 16 path_f) statat_exists_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) statat_exists_model [] := by
  sys_norm

/-- `2^32 - 100` in a0 IS AT_FDCWD: the cast keeps the low 32 bits.
probe: testing/syscall-check/tests/readlinkat_dirfd.c#conform -- low-half -/
theorem readlinkat_low_half_is_at_fdcwd (o : outcome SyscallEffect) :
    syscall_spec (readlinkat_call (Z_to_bv 64 (2 ^ 32 - 100)) 64 path_f) statat_exists_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) statat_exists_model [] := by
  sys_norm

/-- …and so is a register whose high half is garbage over the same low
half.
probe: testing/syscall-check/tests/readlinkat_dirfd.c#conform -- mixed-half -/
theorem readlinkat_mixed_half_is_at_fdcwd (o : outcome SyscallEffect) :
    syscall_spec (readlinkat_call (Z_to_bv 64 0xDEADBEEFFFFFFF9C) 64 path_f) statat_exists_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) statat_exists_model [] := by
  sys_norm

/-- A register of all ones is dirfd -1 after the `int` cast, no
descriptor at all: declined, where a model answering -EINVAL would have
rejected Linux's -EBADF (`path_init`, fs/namei.c:2610-2611, v6.18.46).  Stated on
the spec after `fd32`, the cast the table applies.
kernel: fs/stat.c:readlinkat; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/namei.c:path_init@v6.18.46 -/
theorem readlinkat_minus_one_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    readlinkat_spec (fd32 (Z_to_bv 64 (-1))) i m o ↔ o = Unmodeled := by
  sys_norm

/-! ## newfstatat (79): the flag word first

`vfs_statx` (fs/stat.c:341-363, v6.18.46) answers -EINVAL for any flag bit outside
AT_SYMLINK_NOFOLLOW | AT_NO_AUTOMOUNT | AT_EMPTY_PATH | AT_STATX_SYNC_TYPE
(:348-350) BEFORE `filename_lookup` (:353) hands back the pathname's
stashed error, so the flag word outranks everything below.  The model
interprets 0 and AT_SYMLINK_NOFOLLOW and declines every other word,
including the three Linux accepts: the decline is a coverage gap — for
AT_EMPTY_PATH and AT_NO_AUTOMOUNT Linux answers a definite value the model
has no state to derive — and the pins that offer the kernel's own answer
and still require `Unmodeled` are what keep a later arm from turning that
gap into a guess. -/

/-- THE FLAG GATE PRECEDES THE PATHNAME.  AT_SYMLINK_FOLLOW (0x400) is a
word `vfs_statx` refuses (fs/stat.c:348-350, v6.18.46), and it refuses it
before the pathname is looked at: with nothing readable at the pointer
Linux answers -EINVAL and not the -EFAULT `getname` stashed, because the
flag test runs before `filename_lookup` (:353) hands the stashed error
back (fs/namei.c:2702-2703).  The model has not interpreted the word and
declines, and its decline sits at the same place: before the fetch, so no
pathname error is answered under it.
kernel: fs/stat.c:vfs_fstatat,vfs_statx; fs/namei.c:getname_flags,filename_lookup@v6.18.46 -/
theorem flag_gate_precedes_the_pathname (m : Model) (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 (Z_to_bv 64 1024) (statat_input path_none) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- AT_EMPTY_PATH with a NAME: Linux would answer the model's own -ENOENT
for the absent file, and the model still declines, since it has not
interpreted the word.
probe: testing/syscall-check/tests/newfstatat_spec.c#fail-closed -- empty-path-named -/
theorem at_empty_path_is_unmodeled (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 (Z_to_bv 64 AT_EMPTY_PATH) (statat_input path_f)
        statat_absent_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- AT_EMPTY_PATH with the EMPTY name — the shape `vfs_fstatat` kept
rewriting — is declined with every other uninterpreted word: at v6.18.46
its answer turns on the dirfd (`vfs_fstatat`, fs/stat.c:370-375, the
`!name && dfd >= 0` shortcut once `getname_maybe_null`,
include/linux/fs.h:2950-2958, has returned NULL), and the model has not
interpreted the word.  The probe's `empty-path-flag` case records the
decline on a live descriptor.
kernel: fs/stat.c:vfs_fstatat,vfs_statx; include/linux/fs.h:getname_maybe_null@v6.18.46 -/
theorem at_empty_path_empty_name_is_unmodeled (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 (Z_to_bv 64 AT_EMPTY_PATH) (statat_input path_empty)
        statat_absent_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- AT_STATX_FORCE_SYNC (0x2000, include/uapi/linux/fcntl.h:135), a word
`vfs_statx` ACCEPTS — the mask at fs/stat.c:348-350, v6.18.46, admits the
AT_STATX_SYNC_TYPE bits, and `vfs_getattr_nosec` keeps them (:189) — is
declined like every word outside the two interpreted: Linux would answer
the map's -ENOENT here, and the model does not say so.
kernel: fs/stat.c:vfs_statx,vfs_getattr_nosec@v6.18.46 -/
theorem sync_type_flag_is_unmodeled (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 (Z_to_bv 64 0x2000) (statat_input path_f)
        statat_absent_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- AT_NO_AUTOMOUNT (0x800): accepted by Linux (fs/stat.c:348-349, v6.18.46), so
-ENOENT is what it would answer here, and declined by the model.
probe: testing/syscall-check/tests/newfstatat_spec.c#fail-closed -- automount -/
theorem at_no_automount_is_unmodeled (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 (Z_to_bv 64 2048) (statat_input path_f)
        statat_absent_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and the precision it costs: AT_NO_AUTOMOUNT over a PATH_MAX name is
-ENAMETOOLONG on Linux, declined here.
probe: testing/syscall-check/tests/newfstatat_spec.c#fail-closed -- toolong-automount -/
theorem at_no_automount_toolong_is_unmodeled (m : Model) (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 (Z_to_bv 64 2048) (statat_input path_toolong) m o
      ↔ o = Unmodeled := by
  sys_norm

/-- A word Linux REFUSES — AT_SYMLINK_FOLLOW (0x400), -EINVAL at
fs/stat.c:348-350, v6.18.46 — is declined rather than answered: the model has not
interpreted it, and an -EINVAL asserted from the bit pattern would be a
confident answer on every word Linux accepts as well.
probe: testing/syscall-check/tests/newfstatat_spec.c#fail-closed -- bad-flag -/
theorem bad_flag_is_unmodeled (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 (Z_to_bv 64 1024) (statat_input path_f)
        statat_absent_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- The ENOENT Linux would give under AT_NO_AUTOMOUNT is not admitted
either: the decline is about the flag word, whatever the return.
kernel: fs/stat.c:vfs_statx@v6.18.46 -/
theorem at_no_automount_enoent_rejected (m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 (Z_to_bv 64 2048) (statat_input path_f)
        statat_absent_model
        (Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) m' evs) := by
  sys_refute

/-! ## newfstatat: the pathname, with `getname_flags`'s three answers

`vfs_fstatat` (fs/stat.c:365-379, v6.18.46) fetches the name first (:370), through
`getname_maybe_null` (include/linux/fs.h:2950-2958), plain `getname`
(:2944-2947) for both modeled words, i.e. `getname_flags(name, 0)`
(fs/namei.c:136-216, v6.18.46): `strncpy_from_user` (:157) returns -EFAULT for an
unmapped byte (lib/strncpy_from_user.c:113-155) and the negative length
is returned as it is (:161-165); an empty name is -ENOENT (:167-171); a
name that fills EMBEDDED_NAME_MAX is redone at PATH_MAX (:180-195) and a
PATH_MAX-long copy is -ENAMETOOLONG (:207-211).  `filename_lookup`
(fs/namei.c:2697-2703, v6.18.46) returns the stashed error before any walk, so all
three preempt the dirfd.  Every answering arm carries the copy-in ledger
(`record_copyins`): the bytes through the NUL, through the first
unreadable byte, or PATH_MAX. -/

/-- A NULL pathname is -EFAULT, and the ledger charges the ONE byte
`strncpy_from_user` attempted: the fetch happened.  Holds on every model:
the file system is not consulted.
kernel: fs/stat.c:vfs_fstatat; fs/namei.c:getname_flags,path_init; lib/strncpy_from_user.c:strncpy_from_user@v6.18.46 -/
theorem null_pathname_is_efault (m : Model) (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0 0 statat_null_input m o
      ↔ o = Ok (with_copyins [(0, 1)] (mkEffect (errno_ret EFAULT) [] [])) m [] := by
  sys_norm

/-- …not -ENAMETOOLONG: `strncpy_from_user`'s negative return is handed
back as it is (fs/namei.c:161-165, v6.18.46), never turned into the PATH_MAX
answer.
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:ret=-ENAMETOOLONG -- fault-null -/
theorem null_pathname_is_not_enametoolong (m m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0 0 statat_null_input m
        (Ok (with_copyins [(0, 1)] (mkEffect (errno_ret ENAMETOOLONG) [] [])) m' evs) := by
  sys_refute

/-- …and an immediate fault still records its one attempted byte: the
empty ledger is refused.
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:drop-copyins -- fault-null -/
theorem null_pathname_ledger_not_dropped (m m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0 0 statat_null_input m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- …and exactly one: a second byte was never asked for.
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:grow-copyins:1 -- fault-null -/
theorem null_pathname_ledger_not_grown (m m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0 0 statat_null_input m
        (Ok (with_copyins [(0, 2)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  sys_refute

/-- The fault PREEMPTS THE DIRFD: with dirfd 5, which the process does not
hold, the answer is still -EFAULT and not -EBADF, because
`filename_lookup` returns the stashed `ERR_PTR` (fs/namei.c:2702-2703, v6.18.46)
before `path_init` ever reads `nd->dfd`.
probe: testing/syscall-check/tests/newfstatat_spec.c#conform -- fault-null-dirfd -/
theorem null_pathname_preempts_the_dirfd (m : Model) (o : outcome SyscallEffect) :
    newfstatat_spec 5 0 0 statat_null_input m o
      ↔ o = Ok (with_copyins [(0, 1)] (mkEffect (errno_ret EFAULT) [] [])) m [] := by
  sys_norm

/-- Mapped bytes whose NUL is unmapped: -EFAULT, with the two bytes
attempted in the ledger — the content byte and the faulting one.
probe: testing/syscall-check/tests/newfstatat_spec.c#conform -- fault-runoff -/
theorem runoff_pathname_is_efault (m : Model) (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_runoff) m o
      ↔ o = Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret EFAULT) [] [])) m [] := by
  sys_norm

/-- The run-off fetch keeps its attempted range: not dropped…
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:drop-copyins -- fault-runoff -/
theorem runoff_ledger_not_dropped (m m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_runoff) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- …and it ends exactly at the first unmapped byte.
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:grow-copyins:1 -- fault-runoff -/
theorem runoff_ledger_not_grown (m m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_runoff) m
        (Ok (with_copyins [(0x2000, 3)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  sys_refute

/-- An unreadable pathname pointer is -EFAULT and never the -ENOENT of an
absent file: the walk that would answer -ENOENT needs a name it never
got.
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:mem-none -- absent -/
theorem unreadable_pathname_is_not_enoent (m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_none) statat_absent_model
        (Ok (with_copyins [(0x2000, 1)] (mkEffect (errno_ret ENOENT) [] [])) m' evs) := by
  sys_refute

/-- …its only admissible answer is -EFAULT over the one attempted byte.
probe: testing/syscall-check/tests/newfstatat_spec.c#conform --mutate newfstatat:mem-none,ret=-EFAULT -- absent -/
theorem unreadable_pathname_is_efault (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_none) statat_absent_model o
      ↔ o = Ok (with_copyins [(0x2000, 1)] (mkEffect (errno_ret EFAULT) [] [])) statat_absent_model [] := by
  sys_norm

/-- THE PATH_MAX ARM, over ANY pathname memory whose walk finds no NUL
within PATH_MAX and whose fetch charged PATH_MAX bytes: -ENAMETOOLONG
(`getname_flags`, fs/namei.c:207-211, v6.18.46), the ledger the whole range
strncpy_from_user was asked for (:195), and the dirfd never reached — so
it is stated for every dirfd.  The memory is SYMBOLIC on purpose: a
concrete 4096-byte walk is one the kernel may not evaluate (`path_toolong`'s
note), and a matcher reduced over a closed discriminant of that depth is
what the kernel is then asked to check.  The concrete pins below
instantiate this with the two closed-form readings.
kernel: fs/stat.c:vfs_fstatat; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem toolong_arm_iff (mem : word → Option byte)
    (h1 : read_cstr mem 0x2000 = CstrTooLong)
    (h2 : cstr_access_len_aux mem 0x2000 path_max = 4096)
    (dirfd : word) (m : Model) (o : outcome SyscallEffect) :
    newfstatat_spec dirfd 0x2000 0 (statat_input mem) m o
      ↔ o = Ok (with_copyins [(0x2000, 4096)] (mkEffect (errno_ret ENAMETOOLONG) [] [])) m [] := by
  -- Not `sys_norm`: the normalizer takes no hypotheses, so its first pass
  -- leaves the two SYMBOLIC reads stuck; `h1`/`h2` rewrite them, and the
  -- second pass finishes what one pass does on a closed memory.
  sys_simp_pass +decide
  simp only [h1, h2]
  sys_simp_pass +decide

/-- 4096 bytes with no NUL: -ENAMETOOLONG, and the ledger is the whole
PATH_MAX range strncpy_from_user was asked for (`getname_flags`,
fs/namei.c:195 and :207-211, v6.18.46).  The arm above at the 4096-byte
fixture.
kernel: fs/stat.c:vfs_fstatat; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem toolong_pathname_is_enametoolong (m : Model) (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_toolong) m o
      ↔ o = Ok (with_copyins [(0x2000, 4096)] (mkEffect (errno_ret ENAMETOOLONG) [] [])) m [] :=
  toolong_arm_iff path_toolong read_cstr_path_toolong len_path_toolong (fd32 AT_FDCWD) m o

/-- The three path failures are not interchangeable: not -ENOENT…
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:ret=-ENOENT -- toolong -/
theorem toolong_is_not_enoent (m m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_toolong) m
        (Ok (with_copyins [(0x2000, 4096)] (mkEffect (errno_ret ENOENT) [] [])) m' evs) := by
  rw [toolong_arm_iff path_toolong read_cstr_path_toolong len_path_toolong]
  sys_refute

/-- …nor -EFAULT: every byte of the run was readable.
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:ret=-EFAULT -- toolong -/
theorem toolong_is_not_efault (m m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_toolong) m
        (Ok (with_copyins [(0x2000, 4096)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  rw [toolong_arm_iff path_toolong read_cstr_path_toolong len_path_toolong]
  sys_refute

/-- -ENAMETOOLONG keeps the whole PATH_MAX range it attempted…
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:drop-copyins -- toolong -/
theorem toolong_ledger_not_dropped (m m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_toolong) m
        (Ok (mkEffect (errno_ret ENAMETOOLONG) [] []) m' evs) := by
  rw [toolong_arm_iff path_toolong read_cstr_path_toolong len_path_toolong]
  sys_refute

/-- …and not a byte past it: the fetch stops at PATH_MAX.
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:grow-copyins:1 -- toolong -/
theorem toolong_ledger_not_grown (m m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_toolong) m
        (Ok (with_copyins [(0x2000, 4097)] (mkEffect (errno_ret ENAMETOOLONG) [] [])) m' evs) := by
  rw [toolong_arm_iff path_toolong read_cstr_path_toolong len_path_toolong]
  sys_refute

/-- The too-long name PREEMPTS THE DIRFD: with dirfd 5 the answer is
-ENAMETOOLONG, and the -EBADF a dirfd-first kernel would give is refused
(`filename_lookup`, fs/namei.c:2702-2703, v6.18.46, before `path_init`).
probe: testing/syscall-check/tests/newfstatat_spec.c#conform -- toolong-dirfd -/
theorem toolong_preempts_the_dirfd (m : Model) (o : outcome SyscallEffect) :
    newfstatat_spec 5 0x2000 0 (statat_input path_toolong) m o
      ↔ o = Ok (with_copyins [(0x2000, 4096)] (mkEffect (errno_ret ENAMETOOLONG) [] [])) m [] :=
  toolong_arm_iff path_toolong read_cstr_path_toolong len_path_toolong 5 m o

/-- …the dirfd's -EBADF, which getname-first forbids.
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:ret=-EBADF -- toolong-dirfd -/
theorem toolong_dirfd_ebadf_rejected (m m' : Model) (evs : List event) :
    ¬ newfstatat_spec 5 0x2000 0 (statat_input path_toolong) m
        (Ok (with_copyins [(0x2000, 4096)] (mkEffect (errno_ret EBADF) [] [])) m' evs) := by
  rw [toolong_arm_iff path_toolong read_cstr_path_toolong len_path_toolong]
  sys_refute

/-- The empty pathname is -ENOENT: `getname_flags` answers it for a
zero-length copy without LOOKUP_EMPTY (fs/namei.c:167-171, v6.18.46), and no
modeled flag word sets that bit.  The ledger is the one NUL that
terminated it.
kernel: fs/stat.c:vfs_fstatat; include/linux/fs.h:getname_maybe_null; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem empty_pathname_is_enoent (m : Model) (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_empty) m o
      ↔ o = Ok (with_copyins [(0x2000, 1)] (mkEffect (errno_ret ENOENT) [] [])) m [] := by
  sys_norm

/-- …and it still costs the NUL that terminated it.
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:drop-copyins -- empty -/
theorem empty_pathname_ledger_not_dropped (m m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_empty) m
        (Ok (mkEffect (errno_ret ENOENT) [] []) m' evs) := by
  sys_refute

/-- The empty pathname PREEMPTS THE DIRFD too: dirfd 5 is never reached.
probe: testing/syscall-check/tests/newfstatat_spec.c#conform -- empty-dirfd -/
theorem empty_pathname_preempts_the_dirfd (m : Model) (o : outcome SyscallEffect) :
    newfstatat_spec 5 0x2000 0 (statat_input path_empty) m o
      ↔ o = Ok (with_copyins [(0x2000, 1)] (mkEffect (errno_ret ENOENT) [] [])) m [] := by
  sys_norm

/-- …likewise refusing the dirfd's -EBADF.
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:ret=-EBADF -- empty-dirfd -/
theorem empty_dirfd_ebadf_rejected (m m' : Model) (evs : List event) :
    ¬ newfstatat_spec 5 0x2000 0 (statat_input path_empty) m
        (Ok (with_copyins [(0x2000, 1)] (mkEffect (errno_ret EBADF) [] [])) m' evs) := by
  sys_refute

/-! ## newfstatat: then the dirfd, then the file

`path_init` (fs/namei.c:2540-2645, v6.18.46) takes the working directory for
AT_FDCWD (:2590-2604) and, for any other number, a descriptor that must
be open (-EBADF, :2610-2611) and a directory (-ENOTDIR, :2621-2622): a
starting point the model cannot name, so every dirfd but AT_FDCWD is
declined — a coverage gap, and the pins offer Linux's answers and still
refuse them.  Under AT_FDCWD, "." is the working directory (`handle_dots`,
fs/namei.c:2096-2132, v6.18.46) and declined for its metadata; any other name the
map does not hold is the walk's -ENOENT (`walk_component` → `step_into`,
:1984-2022, where `traverse_mounts` answers it for a negative dentry at
:1537-1538 and the RCU walk at :2001-2002); a name the map holds would
succeed and is declined. -/

/-- The absent file is -ENOENT, and the pathname WAS copied in to reach
that answer: the two bytes `getname_flags` read are in the ledger.  Rocq's
`newfstatat_pathname_copyin_is_charged`, control conjunct.
kernel: fs/stat.c:newfstatat,vfs_fstatat,vfs_statx; fs/namei.c:getname_flags,path_init,step_into,traverse_mounts@v6.18.46 -/
theorem absent_file_is_enoent (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_f) statat_absent_model o
      ↔ o = Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model [] := by
  sys_norm

/-- The ledger is not optional: the effect a spec with no `record_copyins`
wrapper would produce is refused.  A copy-in ledger is model-internal
state no observation of a real execution reveals, so only a literal range
written down here separates the model from an empty one.
rocq-twin: newfstatat_pathname_copyin_is_charged
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:drop-copyins -- absent -/
theorem absent_file_ledger_not_dropped (m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_f) statat_absent_model
        (Ok (mkEffect (errno_ret ENOENT) [] []) m' evs) := by
  sys_refute

/-- Nor may it over-report: the fetch stops at the NUL, at two bytes.
rocq-twin: newfstatat_pathname_copyin_is_charged
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:grow-copyins:1 -- absent -/
theorem absent_file_ledger_not_grown (m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_f) statat_absent_model
        (Ok (with_copyins [(0x2000, 3)] (mkEffect (errno_ret ENOENT) [] [])) m' evs) := by
  sys_refute

/-- Nor start anywhere but the pathname pointer.
rocq-twin: newfstatat_pathname_copyin_is_charged
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:shift-copyins:1 -- absent -/
theorem absent_file_ledger_not_shifted (m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_f) statat_absent_model
        (Ok (with_copyins [(0x2001, 2)] (mkEffect (errno_ret ENOENT) [] [])) m' evs) := by
  sys_refute

/-- A kernel claiming the stat of an absent file succeeded is refused.
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:ret=0 -- absent -/
theorem absent_file_success_rejected (m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_f) statat_absent_model
        (Ok (with_copyins [(0x2000, 2)] (mkEffect 0 [] [])) m' evs) := by
  sys_refute

/-- -EFAULT where the path was fetched fine: refused.  With `statbuf`
never written on a failing arm, the only -EFAULT is the pathname's.
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:ret=-EFAULT -- absent -/
theorem absent_file_efault_rejected (m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_f) statat_absent_model
        (Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret EFAULT) [] [])) m' evs) := by
  sys_refute

/-- -EINVAL on a flag word `vfs_statx` accepts: refused.
probe: testing/syscall-check/tests/newfstatat_spec.c#reject --mutate newfstatat:ret=-EINVAL -- absent -/
theorem absent_file_einval_rejected (m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_f) statat_absent_model
        (Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret EINVAL) [] [])) m' evs) := by
  sys_refute

/-- The `lstat` spelling, AT_SYMLINK_NOFOLLOW: the model has no symlinks,
so the answer is identical, and the kernel reads the bit only to drop
LOOKUP_FOLLOW (`statx_lookup_flags`, fs/stat.c:288-289).
kernel: fs/stat.c:vfs_statx,statx_lookup_flags; fs/namei.c:path_init,step_into,traverse_mounts@v6.18.46 -/
theorem absent_file_nofollow_is_enoent (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW) (statat_input path_f)
        statat_absent_model o
      ↔ o = Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model [] := by
  sys_norm

/-- A dirfd the process does not hold is declined: Linux answers -EBADF
(`path_init`, fs/namei.c:2610-2611, v6.18.46) or, for a live non-directory, -ENOTDIR
(:2621-2622), or walks from a directory the model cannot name.
probe: testing/syscall-check/tests/newfstatat_spec.c#fail-closed -- bad-dirfd -/
theorem other_dirfd_is_unmodeled (o : outcome SyscallEffect) :
    newfstatat_spec 5 0x2000 0 (statat_input path_f) statat_absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …not even on an -ENOENT claim: the decline is about the dirfd.
probe: testing/syscall-check/tests/newfstatat_spec.c#fail-closed --mutate newfstatat:ret=-ENOENT -- bad-dirfd -/
theorem other_dirfd_enoent_rejected (m' : Model) (evs : List event) :
    ¬ newfstatat_spec 5 0x2000 0 (statat_input path_f) statat_absent_model
        (Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) m' evs) := by
  sys_refute

/-- A LIVE descriptor that is not a directory as dirfd is declined too:
the channel at fd 0 is one Linux answers -ENOTDIR for (`path_init`,
fs/namei.c:2621-2622, v6.18.46), and the spec reads the number alone.  The
probe's `live-dirfd` case records the same decline on the file it opened.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem live_dirfd_is_unmodeled (o : outcome SyscallEffect) :
    newfstatat_spec 0 0x2000 0 (statat_input path_f) statat_absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- "." is the working directory, and a directory's metadata is as absent
from the model as a file's: declined, where Linux succeeds.
probe: testing/syscall-check/tests/newfstatat_spec.c#fail-closed -- dot -/
theorem dot_is_unmodeled (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_dot) statat_absent_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and the -ENOENT the map would give for "." is refused: the dot path
is declined BEFORE the lookup.
kernel: fs/namei.c:handle_dots@v6.18.46 -/
theorem dot_enoent_rejected (m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_dot) statat_absent_model
        (Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) m' evs) := by
  sys_refute

/-- ".." IS NOT DECLINED, and that is a RECORDED DIVERGENCE, stated as
what it is: Linux resolves it to the parent (`handle_dots`,
fs/namei.c:2096-2132, v6.18.46) and stats it, and this spec lets it fall
to the map's -ENOENT — the shape
bugs/newfstatat-flat-namespace-false-rejections.md carries, which the
probe admits only under the mutation that makes the kernel say the
model's answer.
probe: testing/syscall-check/tests/newfstatat_spec.c#conform --mutate newfstatat:ret=-ENOENT -- dotdot -/
theorem dotdot_is_the_maps_enoent (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_dotdot) statat_absent_model o
      ↔ o = Ok (with_copyins [(0x2000, 3)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model [] := by
  sys_norm

/-- "f/x" WITH "f" A REGULAR FILE, the second recorded shape: Linux walks
into "f" and answers -ENOTDIR (`link_path_walk`, fs/namei.c:2529-2534,
v6.18.46), and this spec, whose map has no directories, answers the
-ENOENT of a key it does not hold.
probe: testing/syscall-check/tests/newfstatat_spec.c#conform --mutate newfstatat:ret=-ENOENT -- enotdir -/
theorem slash_component_is_the_maps_enoent (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_fx) statat_exists_model o
      ↔ o = Ok (with_copyins [(0x2000, 4)] (mkEffect (errno_ret ENOENT) [] [])) statat_exists_model [] := by
  sys_norm

/-- A file the map holds would succeed on Linux, delivering 128 bytes the
model has no metadata for: declined.
probe: testing/syscall-check/tests/newfstatat_spec.c#fail-closed -- exists -/
theorem existing_file_is_unmodeled (o : outcome SyscallEffect) :
    newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_f) statat_exists_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and the decline is about the MODEL's file system, not the return: an
-ENOENT claimed for a file that exists is refused too.
probe: testing/syscall-check/tests/newfstatat_spec.c#fail-closed --mutate newfstatat:ret=-ENOENT -- exists -/
theorem existing_file_enoent_rejected (m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_f) statat_exists_model
        (Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) m' evs) := by
  sys_refute

/-! ### The dispatcher: syscall 79, `int dfd` and `int flag`

`__NR3264_fstatat` is 79 (include/uapi/asm-generic/unistd.h:210-211, v6.18.46, the
`__SC_3264` resolving to `sys_newfstatat` on a 64-bit `long`;
`79 64 newfstatat sys_newfstatat` in scripts/syscall.tbl:102).  `dfd` and
`flag` are both `int` in the `SYSCALL_DEFINE4` (fs/stat.c:536-537, v6.18.46), so
each register's high half is dropped by `__SC_CAST`
(include/linux/syscalls.h:132) under `__SYSCALL_DEFINEx`
(arch/riscv/include/asm/syscall_wrapper.h:82-88). -/

/-- Syscall 79 on the absent file, through the table: the same -ENOENT
and the same two-byte ledger.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_fstatat; fs/stat.c:newfstatat,vfs_fstatat,vfs_statx; fs/namei.c:path_init,step_into,traverse_mounts@v6.18.46 -/
theorem sysno_79_is_newfstatat (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 79 [AT_FDCWD, 0x2000, 0, 0, 0, 0] path_f (fun _ => none))
        statat_absent_model o
      ↔ o = Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model [] := by
  sys_norm

/-- A NULL `statbuf` is never written on this arm, so -ENOENT stands: the
pointer in a2 is 0 in every call above, and the spec does not take it.
probe: testing/syscall-check/tests/newfstatat_spec.c#conform -- absent-nullbuf -/
theorem absent_file_null_statbuf_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (statat_call AT_FDCWD 0 path_f) statat_absent_model o
      ↔ o = Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model [] := by
  sys_norm

/-- …and no errno arm delivers a byte: `SYSCALL_DEFINE4(newfstatat)`
reaches `cp_new_stat` only once `vfs_fstatat` has returned 0
(fs/stat.c:542-546, v6.18.46), so an -ENOENT that also wrote the struct
is refused.
kernel: fs/stat.c:newfstatat,cp_new_stat@v6.18.46 -/
theorem absent_file_smuggled_write_rejected (m' : Model) (evs : List event) :
    ¬ newfstatat_spec (fd32 AT_FDCWD) 0x2000 0 (statat_input path_f) statat_absent_model
        (Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [(0, zero_stat)] [])) m' evs) := by
  sys_refute

/-- A flag register of `2^32` is flag 0 after the `int` cast.
probe: testing/syscall-check/tests/newfstatat_spec.c#conform -- hi-flag -/
theorem hi_flag_truncates_to_zero (o : outcome SyscallEffect) :
    syscall_spec (statat_call AT_FDCWD (Z_to_bv 64 (2 ^ 32)) path_f) statat_absent_model o
      ↔ o = Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model [] := by
  sys_norm

/-- …and `0xDEADBEEF_00000100` is AT_SYMLINK_NOFOLLOW.
probe: testing/syscall-check/tests/newfstatat_spec.c#conform -- hi-flag-nofollow -/
theorem hi_flag_nofollow_truncates (o : outcome SyscallEffect) :
    syscall_spec (statat_call AT_FDCWD (Z_to_bv 64 0xDEADBEEF00000100) path_f) statat_absent_model o
      ↔ o = Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model [] := by
  sys_norm

/-- A dirfd register of `2^32 - 100` IS AT_FDCWD after the `int` cast, and
the call is answered.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_fstatat; fs/stat.c:newfstatat; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/namei.c:path_init,step_into,traverse_mounts@v6.18.46 -/
theorem dirfd_low_half_is_at_fdcwd (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 79 [Z_to_bv 64 (2 ^ 32 - 100), 0x2000, 0, 0, 0, 0] path_f
                   (fun _ => none)) statat_absent_model o
      ↔ o = Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model [] := by
  sys_norm

/-! ## fstat (80): `vfs_fstat` resolves the descriptor first

`SYSCALL_DEFINE2(newfstat, unsigned int, fd, …)` (fs/stat.c:550-560, v6.18.46) is
`vfs_fstat(fd, &stat)` (:555), whose error is returned as it is
(:556-557), and only then `cp_new_stat(&stat, statbuf)` (:559).
`vfs_fstat` (:276-282) takes `CLASS(fd_raw, f)(fd)` (:278) and answers
-EBADF on `fd_empty(f)` (:279-280) before anything can read `statbuf`, so
a closed fd is -EBADF whatever the pointer, and writes nothing. -/

/-- A closed fd is -EBADF and nothing else, on any memory: `vfs_fstat`
(fs/stat.c:279-280, v6.18.46) decides before `statbuf` is looked at.  The
probe's `closed` and `unopened` cases record it on fd 3 (opened, then
closed), on 9999 and on -1; the fixture's 9 is the number its table never
held.
kernel: fs/stat.c:newfstat,vfs_fstat@v6.18.46 -/
theorem closed_fd_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    fstat_spec 9 4096 i fstat_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) fstat_model [] := by
  sys_norm

/-- A closed fd claiming the stat succeeded: refused (the probe's
`ret=0 -- closed` and `fstat#2:ret=0 -- unopened` lies).
kernel: fs/stat.c:newfstat,vfs_fstat@v6.18.46 -/
theorem closed_fd_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fstat_spec 9 4096 i fstat_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- `cp_new_stat`'s -EFAULT, which `vfs_fstat` preempts: on a closed fd
with a `statbuf` `access_ok` refuses, the answer is still -EBADF.
kernel: fs/stat.c:newfstat,vfs_fstat@v6.18.46 -/
theorem closed_fd_is_not_efault (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fstat_spec 9 (Z_to_bv 64 (2 ^ 63)) i fstat_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- …and a `statbuf` past every address space still yields -EBADF (the
probe's `wildbuf` case, at `0x7FFFFFFFFFFFF000` on its closed fd 3).
kernel: fs/stat.c:newfstat,vfs_fstat@v6.18.46 -/
theorem closed_fd_wild_statbuf_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    fstat_spec 9 (Z_to_bv 64 (2 ^ 63)) i fstat_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) fstat_model [] := by
  sys_norm

/-- A NULL `statbuf` is never written on this arm, so -EBADF stands (the
probe's `nullbuf` case, on its closed fd 3).
kernel: fs/stat.c:newfstat,vfs_fstat@v6.18.46 -/
theorem closed_fd_null_statbuf_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    fstat_spec 9 0 i fstat_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) fstat_model [] := by
  sys_norm

/-- …and the -EFAULT a statbuf-first kernel would give for NULL is refused
(the probe's `ret=-EFAULT -- nullbuf` lie).
kernel: fs/stat.c:newfstat,vfs_fstat@v6.18.46 -/
theorem closed_fd_null_statbuf_is_not_efault (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fstat_spec 9 0 i fstat_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- An -EBADF that also delivered the struct: `cp_new_stat` has not run,
so no byte lands (the probe's `smuggle-write:a1:128 -- closed` lie).
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem closed_fd_smuggled_write_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fstat_spec 9 4096 i fstat_model
        (Ok (mkEffect (errno_ret EBADF) [(4096, zero_stat)] []) m' evs) := by
  sys_refute

/-- …or that merely zeroed the statbuf (`smuggle-zeros:a1:128 -- closed`).
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem closed_fd_smuggled_zeros_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fstat_spec 9 4096 i fstat_model
        (Ok (mkEffect (errno_ret EBADF) [] [(4096, 128)]) m' evs) := by
  sys_refute

/-- …or that claimed to have READ it: `fstat` takes its descriptor in a
register and reads no user byte at all (`smuggle-copyin:a1:128 -- closed`).
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem closed_fd_smuggled_copyin_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fstat_spec 9 4096 i fstat_model
        (Ok (with_copyins [(4096, 128)] (mkEffect (errno_ret EBADF) [] [])) m' evs) := by
  sys_refute

/-- A kernel calling a LIVE fd closed is refused: the model resolves the
descriptor from its own table (the probe's `ret=-EBADF -- wfile` lie, on
the fd it had just created).
kernel: fs/stat.c:vfs_fstat@v6.18.46 -/
theorem live_fd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 9 4096 fstat_input fstat_kinds_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-! ## fstat: `cp_new_stat`'s `copy_to_user`, in the three bands

Past an open file, `cp_new_stat` (fs/stat.c:470-507, v6.18.46) fills its stack copy
and hands 128 bytes to one `copy_to_user` (:506), which asks
`access_ok(to, n)` over the whole range before a byte moves
(include/linux/uaccess.h:190-200, v6.18.46, :195; `__access_ok`,
include/asm-generic/access_ok.h:31-41) and answers -EFAULT.  A range
`access_ok` admits but memory does not wholly back is `raw_copy_to_user`'s
partial write (:197), which the model declines: `copy_to_user` commits a
prefix and then answers -EFAULT, and the model has no vocabulary for a
half-written struct (the shape Rocq's `Stat.fstat_file_spec` names beside
`uname` and `gettimeofday`), so it cannot say how long the prefix is — a
coverage gap, not an empty intersection. -/

/-- `access_ok` refuses the 128-byte range at `2^63`: -EFAULT, exact,
before a byte moves, on any memory.
rocq-twin: fstat_access_ok_fault
probe: testing/syscall-check/tests/fstat_spec.c#conform -- livefault -/
theorem access_ok_fault (i : SyscallInput) (o : outcome SyscallEffect) :
    fstat_spec 3 (Z_to_bv 64 (2 ^ 63)) i fstat_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) fstat_model [] := by
  sys_norm

/-- …and the success a kernel that had written it would report is refused.
probe: testing/syscall-check/tests/fstat_spec.c#reject --mutate fstat:ret=0 -- livefault -/
theorem access_ok_fault_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 (Z_to_bv 64 (2 ^ 63)) i fstat_model
        (Ok (mkEffect 0 [(Z_to_bv 64 (2 ^ 63), stat_truthful)] []) m' evs) := by
  sys_refute

/-- A range `access_ok` ADMITS but memory does not wholly back is declined
rather than faulted: one byte short of 128 is the whole difference.
rocq-twin: fstat_one_byte_short_is_unmodeled
kernel: include/linux/uaccess.h:_inline_copy_to_user; fs/stat.c:cp_new_stat@v6.18.46 -/
theorem one_byte_short_is_unmodeled (o : outcome SyscallEffect) :
    fstat_spec 3 4096 fstat_input_short fstat_model o ↔ o = Unmodeled := by
  sys_norm

/-- THE BOUNDARY OF `access_ok`, one byte each way.  `__access_ok`
(include/asm-generic/access_ok.h:40, v6.18.46) is `(size <= limit) &&
(addr <= (limit - size))`, so a 128-byte range ending exactly at the
limit is admitted and the walk then decides — here the fixture memory
does not back it, and the arm declines rather than faults…
kernel: include/asm-generic/access_ok.h:__access_ok; include/linux/uaccess.h:_inline_copy_to_user; fs/stat.c:cp_new_stat@v6.18.46 -/
theorem access_ok_last_zone_is_walked (o : outcome SyscallEffect) :
    fstat_spec 3 (Z_to_bv 64 (2 ^ 47 - 128)) fstat_input fstat_model o ↔ o = Unmodeled := by
  sys_norm

/-- …while one byte higher the range crosses the limit and `copy_to_user`
refuses it before a byte moves: -EFAULT, on any memory.
kernel: include/asm-generic/access_ok.h:__access_ok; include/linux/uaccess.h:_inline_copy_to_user; fs/stat.c:cp_new_stat@v6.18.46 -/
theorem access_ok_past_the_limit_faults (i : SyscallInput) (o : outcome SyscallEffect) :
    fstat_spec 3 (Z_to_bv 64 (2 ^ 47 - 127)) i fstat_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) fstat_model [] := by
  sys_norm

/-- …so neither the full delivery nor -EFAULT is admitted there.
kernel: include/linux/uaccess.h:_inline_copy_to_user; fs/stat.c:cp_new_stat@v6.18.46 -/
theorem one_byte_short_efault_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input_short fstat_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-! ## fstat: the delivered `struct stat`

WHICH REASON FROM THE TOP OF ROCQ'S `Checks/Examples.v`: the fourth, for
every rejecting example, and the first for the accepting controls.  The
rejecting direction needs a kernel behaving inadmissibly — one that
reports a length its own S_IFREG contradicts, that scribbles
`cp_new_stat`'s cleared padding, that names no file type at all, or that
changes a file's inode between two stats of it.  No Linux does any of
those, so `fstat_spec.c` cannot construct them and `--mutate` cannot
either: the harness's operators move a write's address, width and every
byte at once, and none edits ONE member.  The accepting controls are not
decoration: without them each rejection could be an artefact of some
other field rather than of the member it names.

The kernel each claim rests on: `cp_new_stat` (fs/stat.c:470-507, v6.18.46) clears
its stack copy (`INIT_STRUCT_STAT_PADDING`, :483, the `memset` of
:466-468), assigns the members (:484-505) and copies all 128 bytes at once
(:506); `generic_fillattr` (:82-113) read `i_size` into `stat->size`
(:95), which `cp_new_stat` copies to `st_size` (:495). -/

/-- THE ADMITTED SET on the unpinned file: 0, the 128 bytes at `statbuf`,
and the pin recorded — for any bytes that are well-formed
(`stat_buf_wf`: width 128, cleared padding, a real type) and honour the
size implication for a nine-byte file.  Nothing else: not an errno, not a
decline, not a delivery elsewhere.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat,generic_fillattr@v6.18.46 -/
theorem first_stat_iff (o : outcome SyscallEffect) :
    fstat_spec 3 4096 fstat_input fstat_model o
      ↔ ∃ bs : List byte,
          o = Ok (mkEffect 0 [(4096, bs)] []) (with_statpin fstat_path bs fstat_model) []
          ∧ stat_buf_wf bs = true ∧ stat_size_ok 9 bs = true := by
  sys_norm

/-- The first stat of a file is where its identity enters the model: the
answer is admitted and BECOMES the pin.
rocq-twin: fstat_first_answer_pins
probe: testing/syscall-check/tests/fstat_spec.c#conform -- size -/
theorem first_answer_pins :
    fstat_spec 3 4096 fstat_input fstat_model
      (Ok (mkEffect 0 [(4096, stat_truthful)] []) (with_statpin fstat_path stat_truthful fstat_model) []) := by
  rw [first_stat_iff]
  exact ⟨stat_truthful, rfl, wf_truthful, size9_truthful⟩

/-- …and it MUST become the pin: the same delivery with the model left
unpinned is refused, so a second stat cannot draw afresh.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem first_answer_must_pin (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model
        (Ok (mkEffect 0 [(4096, stat_truthful)] []) fstat_model evs) := by
  -- The hypothesis form, not the goal form: `evs` is the one free variable
  -- here (the model is the fixed, unpinned `fstat_model`), and normalizing
  -- the negated goal leaves the residue `False → ¬ evs = []`, which the
  -- goal form reports as unsolved; reducing `h` itself to `False` closes it.
  intro h
  sys_refute at h

/-- The model does NOT claim the file is regular.  Offered S_IFCHR with
`st_size` 0 — the true answer for the character device
bugs/fs-paths-assumed-regular-files.md exhibits, a path this model
resolves and holds nine bytes for — the spec ADMITS; this is the example
that would fail if the implication in `stat_size_ok` were ever
strengthened to an assertion.
rocq-twin: fstat_character_device_answer_admitted
kernel: include/uapi/linux/stat.h:S_IFCHR; fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem character_device_answer_admitted :
    fstat_spec 3 4096 fstat_input fstat_model
      (Ok (mkEffect 0 [(4096, stat_ifchr_zero)] [])
          (with_statpin fstat_path (stat_ifchr_zero) fstat_model) []) := by
  rw [first_stat_iff]
  exact ⟨stat_ifchr_zero, rfl, wf_ifchr_zero, size9_ifchr_zero⟩

/-- …and the implication BITES on the arm it is about: eight bytes where
the map holds nine, under the kernel's own S_IFREG, is inadmissible.
Paired with the control above, this attributes the rejection to the
length rather than to the type.
rocq-twin: fstat_wrong_size_under_ifreg_rejected
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem wrong_size_under_ifreg_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model
        (Ok (mkEffect 0 [(4096, stat_short_size)] []) m' evs) := by
  sys_refute

/-- A file that GREW must report the new length, not the old one: the
length tracks the map while the identity does not.
rocq-twin: fstat_stale_size_after_growth_rejected
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem stale_size_after_growth_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model_grown_pinned
        (Ok (mkEffect 0 [(4096, stat_truthful)] []) m' evs) := by
  sys_refute

/-- THE ADMITTED SET on a pinned file: the same three conditions with the
pin's stable members repeated, and the model unchanged.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat,generic_fillattr@v6.18.46 -/
theorem pinned_stat_iff (o : outcome SyscallEffect) :
    fstat_spec 3 4096 fstat_input fstat_model_pinned o
      ↔ ∃ bs : List byte,
          o = Ok (mkEffect 0 [(4096, bs)] []) fstat_model_pinned []
          ∧ stat_buf_wf bs = true ∧ stat_size_ok 9 bs = true
          ∧ stat_stable_eqb bs stat_truthful = true := by
  sys_norm

/-- …and on the grown pinned file, with the size obligation at twelve.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat,generic_fillattr@v6.18.46 -/
theorem grown_pinned_stat_iff (o : outcome SyscallEffect) :
    fstat_spec 3 4096 fstat_input fstat_model_grown_pinned o
      ↔ ∃ bs : List byte,
          o = Ok (mkEffect 0 [(4096, bs)] []) fstat_model_grown_pinned []
          ∧ stat_buf_wf bs = true ∧ stat_size_ok 12 bs = true
          ∧ stat_stable_eqb bs stat_truthful = true := by
  sys_norm

/-- The grown file's new length, with new times and blocks against the
old pin, is admitted: stat, write, stat.
rocq-twin: fstat_grown_size_admitted
probe: testing/syscall-check/tests/fstat_spec.c#conform -- twice-grow -/
theorem grown_size_admitted :
    fstat_spec 3 4096 fstat_input fstat_model_grown_pinned
      (Ok (mkEffect 0 [(4096, stat_grown)] []) fstat_model_grown_pinned []) := by
  rw [grown_pinned_stat_iff]
  exact ⟨stat_grown, rfl, wf_grown, size12_grown, stable_grown⟩

/-- `cp_new_stat` clears the whole struct and no assignment covers
`__pad1`, so it is delivered as zero: one nonzero byte there is a kernel
this model refuses.  The probe's `poison-writes:255 -- size` lie is the
nearest recorded one and is refused for another reason — 0xFF in every
byte makes `st_mode`'s type bits `S_IFMT`, no type at all — so the
evidence is the clearing itself.
rocq-twin: fstat_nonzero_pad1_rejected
kernel: fs/stat.c:cp_new_stat,INIT_STRUCT_STAT_PADDING@v6.18.46 -/
theorem nonzero_pad1_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model
        (Ok (mkEffect 0 [(4096, stat_pad1_poisoned)] [])
            m' evs) := by
  sys_refute

/-- …and so is one in `__unused4`/`__unused5`.
rocq-twin: fstat_nonzero_unused45_rejected
kernel: fs/stat.c:cp_new_stat,INIT_STRUCT_STAT_PADDING@v6.18.46 -/
theorem nonzero_unused45_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model
        (Ok (mkEffect 0 [(4096, stat_unused45_poisoned)] []) m' evs) := by
  sys_refute

/-- …and one in `__pad2` (bytes 60..63), the padding member no other
fixture isolates: `stat_buf_wf` reads it on its own.
kernel: fs/stat.c:cp_new_stat,INIT_STRUCT_STAT_PADDING@v6.18.46 -/
theorem nonzero_pad2_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model
        (Ok (mkEffect 0 [(4096, stat_pad2_poisoned)] []) m' evs) := by
  sys_refute

/-- AN ALL-ZERO STRUCT IS THE SHAPE A KERNEL THAT WROTE NOTHING AND SAID IT
DID WOULD PRODUCE, and it is refused by `st_mode` naming no file type.
rocq-twin: fstat_all_zero_struct_rejected
probe: testing/syscall-check/tests/fstat_spec.c#reject --mutate fstat:poison-writes:0 -- size -/
theorem all_zero_struct_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model
        (Ok (mkEffect 0 [(4096, zero_stat)] []) m' evs) := by
  sys_refute

/-- …and so is a type word that is none of the seven: `S_IFMT` itself,
every type bit set, which no inode holds.
rocq-twin: fstat_impossible_type_rejected
kernel: include/uapi/linux/stat.h:S_IFMT; fs/stat.c:generic_fillattr@v6.18.46 -/
theorem impossible_type_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model
        (Ok (mkEffect 0 [(4096, stat_ifmt_type)] []) m' evs) := by
  sys_refute

/-! ### The pin: two stats of one file cannot disagree -/

/-- Once pinned, the same answer is admitted again and the model is left
as it was.
rocq-twin: fstat_pinned_repeat_admitted
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem pinned_repeat_admitted :
    fstat_spec 3 4096 fstat_input fstat_model_pinned
      (Ok (mkEffect 0 [(4096, stat_truthful)] []) fstat_model_pinned []) := by
  rw [pinned_stat_iff]
  exact ⟨stat_truthful, rfl, wf_truthful, size9_truthful, stable_truthful⟩

/-- A later stat that differs in `st_ino` alone — otherwise the same
admissible answer — is refused for disagreeing with the record.  That is
the whole content of "a file keeps its inode for the life of a run"
(`generic_fillattr` reads `inode->i_ino`, fs/stat.c:89).
rocq-twin: fstat_pinned_inode_defector_rejected
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem pinned_inode_defector_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model_pinned
        (Ok (mkEffect 0 [(4096, stat_other_inode)] []) m' evs) := by
  sys_refute

/-- A different `st_blksize` against the pin is refused too — the third
slice `stat_stable_eqb` compares (bytes 56..63), which nothing else
constrains: `generic_fillattr` reads `i_blocksize(inode)` (fs/stat.c:105,
v6.18.46), a property of the inode, not of the call.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem pinned_blksize_defector_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model_pinned
        (Ok (mkEffect 0 [(4096, stat_other_blksize)] []) m' evs) := by
  sys_refute

/-- …though the defector would have been accepted as a FIRST answer, so
the rejection above is about the record, not the number.
rocq-twin: fstat_inode_defector_is_itself_admissible_first
kernel: include/uapi/linux/stat.h:S_IFREG; fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem inode_defector_is_itself_admissible_first :
    fstat_spec 3 4096 fstat_input fstat_model
      (Ok (mkEffect 0 [(4096, stat_other_inode)] [])
          (with_statpin fstat_path (stat_other_inode) fstat_model) []) := by
  rw [first_stat_iff]
  exact ⟨stat_other_inode, rfl, wf_other_inode, size9_other_inode⟩

/-- THE MEMBERS THE PIN DOES NOT HOLD: new timestamps and a new block count
against the same pin are admitted, because every read and write moves
them.  Without this `stat_stable_eqb` could be widened to the whole
buffer and every other pin here would still pass.
rocq-twin: fstat_pinned_new_times_and_blocks_admitted
kernel: include/uapi/linux/stat.h:S_IFREG; fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem pinned_new_times_and_blocks_admitted :
    fstat_spec 3 4096 fstat_input fstat_model_pinned
      (Ok (mkEffect 0 [(4096, stat_new_times)] []) fstat_model_pinned []) := by
  rw [pinned_stat_iff]
  exact ⟨stat_new_times, rfl, wf_new_times, size9_new_times, stable_new_times⟩

/-! ### The write itself: width, address and the empty copy-in ledger -/

/-- The copy is `cp_new_stat`'s one 128-byte copy_to_user (fs/stat.c:506, v6.18.46): 127 bytes is
not a short answer this model has a name for.
rocq-twin: fstat_short_struct_rejected
probe: testing/syscall-check/tests/fstat_spec.c#reject --mutate fstat:trunc-writes:127 -- size -/
theorem short_struct_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model
        (Ok (mkEffect 0 [(4096, stat_short127)] []) m' evs) := by
  sys_refute

/-- …nor 136.
probe: testing/syscall-check/tests/fstat_spec.c#reject --mutate fstat:grow-writes:8 -- size -/
theorem long_struct_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model
        (Ok (mkEffect 0 [(4096, stat_long136)] []) m' evs) := by
  sys_refute

/-- …and it lands at `statbuf`, not one byte past it.
rocq-twin: fstat_shifted_write_rejected
probe: testing/syscall-check/tests/fstat_spec.c#reject --mutate fstat:shift-writes:1 -- size -/
theorem shifted_write_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model
        (Ok (mkEffect 0 [(4097, stat_truthful)] []) m' evs) := by
  sys_refute

/-- A success that delivered no bytes at all is refused: `cp_new_stat`
returns 0 only after the copy (fs/stat.c:506, v6.18.46).
probe: testing/syscall-check/tests/fstat_spec.c#reject --mutate fstat:drop-writes -- size -/
theorem success_without_the_struct_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- Bytes delivered behind an errno return are refused: -EFAULT means
`copy_to_user` reported an uncopied tail, and the model has no partial
delivery.
probe: testing/syscall-check/tests/fstat_spec.c#reject --mutate fstat:ret=-EFAULT -- size -/
theorem struct_behind_efault_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model
        (Ok (mkEffect (errno_ret EFAULT) [(4096, stat_truthful)] []) m' evs) := by
  sys_refute

/-- `fstat` reads no user byte, so the ledger must be empty: a success
claiming to have READ the statbuf is refused.
rocq-twin: fstat_forged_copyin_rejected
probe: testing/syscall-check/tests/fstat_spec.c#reject --mutate fstat:smuggle-copyin:a1:128 -- size -/
theorem forged_copyin_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model
        (Ok (with_copyins [(4096, 128)] (mkEffect 0 [(4096, stat_truthful)] [])) m' evs) := by
  sys_refute

/-! ### The unlinked file, and the pin that dies with it -/

/-- A descriptor whose path the map no longer holds — what `unlinkat`
under an open fd leaves — is declined: Linux answers from the surviving
inode with `st_nlink` 0 (`generic_fillattr`, fs/stat.c:91, v6.18.46), and the model
has no contents to size and no link count to drop.  A coverage gap, kept
because it is also what holds `st_nlink` among the pinned members.
rocq-twin: fstat_unlinked_path_is_unmodeled
kernel: fs/stat.c:generic_fillattr,cp_new_stat@v6.18.46 -/
theorem unlinked_path_is_unmodeled (o : outcome SyscallEffect) :
    fstat_spec 3 4096 fstat_input fstat_model_unlinked o ↔ o = Unmodeled := by
  sys_norm

/-- …so the nine-byte answer is not admitted there either.
kernel: fs/stat.c:generic_fillattr,cp_new_stat@v6.18.46 -/
theorem unlinked_path_delivery_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 3 4096 fstat_input fstat_model_unlinked
        (Ok (mkEffect 0 [(4096, stat_truthful)] []) m' evs) := by
  sys_refute

/-- THE RECEPTIVENESS GUARD on the file arm: a pin that is not
`stat_buf_wf` is declined.  No run builds one — the only writer,
`fstat_file_spec`'s first-stat branch, records bytes `cp_new_stat`
(fs/stat.c:470-507, v6.18.46) delivered and the predicate had just accepted — so
this is a statement about the spec on every `Model`, kept because a spec
that dropped the guard would hand its `choose` an empty set here (nothing
is both well-formed and stable-equal to a record that is not) and be
non-receptive with nothing else to notice.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem malformed_pin_is_declined (o : outcome SyscallEffect) :
    fstat_spec 3 4096 fstat_input fstat_model_badpin o ↔ o = Unmodeled := by
  sys_norm

/-- `unlinkat` destroys the inode, so a pin that outlived the removal would
reject the conforming trace `create f; fstat; unlink f; create f; fstat`:
the remade file is a new inode, whose `i_ino` (`generic_fillattr`,
fs/stat.c:89, v6.18.46) the kernel need not make equal to the old one.
`State.with_fs` drops it: gone when the key goes…
rocq-twin: fstat_pin_dies_with_the_file
model: what `State.with_fs` does to the pin, decided; the kernel argument is on the Rocq twin. -/
theorem pin_dies_with_the_file :
    m_statpins (with_fs [] (with_statpin fstat_path stat_truthful fstat_model)) = [] := rfl

/-- …kept when the same key is merely rewritten.
rocq-twin: fstat_pin_survives_a_rewrite
model: what `State.with_fs` does to the pin, decided; the kernel argument is on the Rocq twin. -/
theorem pin_survives_a_rewrite :
    m_statpins (with_fs [(fstat_path, fstat_data_grown)]
                  (with_statpin fstat_path stat_truthful fstat_model))
      = [(fstat_path, stat_truthful)] := rfl

/-- The recreated file's admitted set is a FIRST stat's: no pin constrains
it, and the delivery becomes the new pin.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat,generic_fillattr@v6.18.46 -/
theorem recreated_stat_iff (o : outcome SyscallEffect) :
    fstat_spec 3 4096 fstat_input fstat_model_recreated o
      ↔ ∃ bs : List byte,
          o = Ok (mkEffect 0 [(4096, bs)] []) (with_statpin fstat_path bs fstat_model_recreated) []
          ∧ stat_buf_wf bs = true ∧ stat_size_ok 9 bs = true := by
  sys_norm

/-- …so with the pin gone, the file created next at that name may report
ANY inode, exactly as a first stat may.  Read beside
`pinned_inode_defector_rejected`, the same struct against a live pin: the
rejection there is about the file's identity and not about the number.
rocq-twin: fstat_recreated_file_takes_a_new_inode
probe: testing/syscall-check/tests/fstat_spec.c#conform -- recreate -/
theorem recreated_file_takes_a_new_inode :
    fstat_spec 3 4096 fstat_input fstat_model_recreated
      (Ok (mkEffect 0 [(4096, stat_other_inode)] [])
          (with_statpin fstat_path (stat_other_inode) fstat_model_recreated) []) := by
  rw [recreated_stat_iff]
  exact ⟨stat_other_inode, rfl, wf_other_inode, size9_other_inode⟩

/-! ### Two files: the size obligation is the descriptor's file, not the kernel's bytes -/

/-- fd 4 names the EMPTY "g": its admitted set carries the size
obligation at zero.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat,generic_fillattr@v6.18.46 -/
theorem empty_file_stat_iff (o : outcome SyscallEffect) :
    fstat_spec 4 4096 fstat_input fstat_two_files_model o
      ↔ ∃ bs : List byte,
          o = Ok (mkEffect 0 [(4096, bs)] []) (with_statpin [103] bs fstat_two_files_model) []
          ∧ stat_buf_wf bs = true ∧ stat_size_ok 0 bs = true := by
  sys_norm

/-- THE PINS ARE PER FILE: with "f" pinned, the first stat of "g" is still
a first stat — its own admitted set, recorded under its own key beside
"f"'s.  Two inodes, two records (`generic_fillattr` reads each
descriptor's own inode, fs/stat.c:88-106, v6.18.46).
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat,generic_fillattr@v6.18.46 -/
theorem empty_file_first_stat_beside_f_pin_iff (o : outcome SyscallEffect) :
    fstat_spec 4 4096 fstat_input fstat_two_files_model_pinned_f o
      ↔ ∃ bs : List byte,
          o = Ok (mkEffect 0 [(4096, bs)] []) (with_statpin [103] bs fstat_two_files_model_pinned_f) []
          ∧ stat_buf_wf bs = true ∧ stat_size_ok 0 bs = true := by
  sys_norm

/-- Ask the model about the EMPTY file and the kernel's nine bytes are
wrong: the answer for fd 3 is refused on fd 4.
probe: testing/syscall-check/tests/fstat_spec.c#reject --mutate fstat:arg0=4 -- two-files -/
theorem nine_bytes_on_the_empty_file_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 4 4096 fstat_input fstat_two_files_model
        (Ok (mkEffect 0 [(4096, stat_truthful)] []) m' evs) := by
  sys_refute

/-! ## fstat: the file kinds

`generic_fillattr` (fs/stat.c:82-113, v6.18.46) reads the inode alone (:88-106), so
the two file kinds share one answer — neither `f_mode` nor `f_flags` is a
member of `struct stat` — and /dev/null answers with its device's
assertions; the four other kinds decline, and the one Rocq answers that
this twin cannot yet declines too. -/

/-- A file opened for WRITING answers as the read-only one does: same
inode, same admitted set (the probe's `wfile` case, on the empty file it
had just created; here the nine-byte one at fd 9).
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat,generic_fillattr@v6.18.46 -/
theorem write_fd_stat_iff (o : outcome SyscallEffect) :
    fstat_spec 9 4096 fstat_input fstat_kinds_model o
      ↔ ∃ bs : List byte,
          o = Ok (mkEffect 0 [(4096, bs)] []) (with_statpin fstat_path bs fstat_kinds_model) []
          ∧ stat_buf_wf bs = true ∧ stat_size_ok 9 bs = true := by
  sys_norm

/-- …and the read-only one on the wider table, identically (the probe's
`rfile` case reopened its empty file O_RDONLY at fd 3).
probe: testing/syscall-check/tests/fstat_spec.c#conform -- rfile -/
theorem read_fd_stat_iff_on_kinds (o : outcome SyscallEffect) :
    fstat_spec 3 4096 fstat_input fstat_kinds_model o
      ↔ ∃ bs : List byte,
          o = Ok (mkEffect 0 [(4096, bs)] []) (with_statpin fstat_path bs fstat_kinds_model) []
          ∧ stat_buf_wf bs = true ∧ stat_size_ok 9 bs = true := by
  sys_norm

/-- …and the size obligation bites through the write descriptor too:
eight bytes under S_IFREG where the map holds nine.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem write_fd_wrong_size_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 9 4096 fstat_input fstat_kinds_model
        (Ok (mkEffect 0 [(4096, stat_short_size)] []) m' evs) := by
  sys_refute

/-- A directory fd is declined: S_IFDIR is the one type bit the model does
know, and a directory's `st_size` and `st_blocks` are the filesystem's
own bookkeeping, not a function of anything the model holds.  A coverage
gap: Linux answers with a definite struct the model has no state for.
The probe's `dir` case records the decline on the directory it opened at
fd 3.
kernel: fs/stat.c:vfs_fstat,cp_new_stat@v6.18.46 -/
theorem dir_is_unmodeled (o : outcome SyscallEffect) :
    fstat_spec 5 4096 fstat_input fstat_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and no errno is admitted for it: the descriptor is live.
kernel: fs/stat.c:vfs_fstat@v6.18.46 -/
theorem dir_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 5 4096 fstat_input fstat_kinds_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- A channel is declined: the model's one name for a pipe, a socket and a
terminal, so S_IFIFO, S_IFSOCK and S_IFCHR are all live and nothing here
chooses between them.  The probe's `chan` case records the decline on fd 1.
kernel: fs/stat.c:vfs_fstat,cp_new_stat@v6.18.46 -/
theorem channel_is_unmodeled (o : outcome SyscallEffect) :
    fstat_spec 0 4096 fstat_input fstat_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- A socket is declined: its mode is a constant (`sock_alloc`,
net/socket.c, v6.18.46) but `st_ino`, `st_dev` and the timestamps are out of reach;
the arm is a matter of writing it, and its pins, not of the model lacking
a mechanism.  The probe's `sock` case records the decline on the socket
it opened at fd 3.
kernel: net/socket.c:sock_alloc; fs/stat.c:vfs_fstat,cp_new_stat@v6.18.46 -/
theorem socket_is_unmodeled (o : outcome SyscallEffect) :
    fstat_spec 6 4096 fstat_input fstat_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- A pipe end is declined: S_IFIFO is known and a pipe's `st_size` and
`st_blocks` are not even the queue's length.
kernel: fs/stat.c:vfs_fstat,cp_new_stat@v6.18.46 -/
theorem pipe_is_unmodeled (o : outcome SyscallEffect) :
    fstat_spec 7 4096 fstat_input fstat_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-! ## fstat: /dev/null, the device the model knows

`init_special_inode` (fs/inode.c:2552-2577, v6.18.46) set S_IFCHR and `i_rdev` when
the node was made (:2554-2559); `generic_fillattr` (fs/stat.c:82-113)
reads them back (:90, :94) and `cp_new_stat` delivers them (:488, :494),
`st_rdev` as `new_encode_dev` (include/linux/kdev_t.h:39-44, v6.18.46) of
`MKDEV(1, 3)` (:12), which is 259; `write_null` (drivers/char/mem.c:418-422)
returns without touching the inode, so `st_size` and `st_blocks` are the
zero `mknod` left.  The pin is keyed under `devnull_path`. -/

/-- THE ADMITTED SET for /dev/null on first stat: well-formed bytes
satisfying the device's assertions, recorded under `devnull_path`.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat,generic_fillattr; fs/inode.c:init_special_inode@v6.18.46 -/
theorem devnull_first_stat_iff (o : outcome SyscallEffect) :
    fstat_spec 4 4096 fstat_input fstat_kinds_model o
      ↔ ∃ bs : List byte,
          o = Ok (mkEffect 0 [(4096, bs)] []) (with_statpin devnull_path bs fstat_kinds_model) []
          ∧ stat_buf_wf bs = true ∧ stat_devnull_ok bs = true := by
  sys_norm

/-- S_IFCHR, `st_rdev` 259, zero size and blocks: admitted, and pinned.
kernel: include/uapi/linux/stat.h:S_IFCHR; include/linux/kdev_t.h:new_encode_dev,MKDEV; fs/inode.c:init_special_inode; drivers/char/mem.c:write_null@v6.18.46 -/
theorem devnull_answer_admitted :
    fstat_spec 4 4096 fstat_input fstat_kinds_model
      (Ok (mkEffect 0 [(4096, devnull_truthful)] [])
          (with_statpin devnull_path devnull_truthful fstat_kinds_model) []) := by
  rw [devnull_first_stat_iff]
  exact ⟨devnull_truthful, rfl, wf_devnull, ok_devnull⟩

/-- A REGULAR-FILE type for the null device is refused: `init_special_inode`
gave the node S_IFCHR.
kernel: fs/inode.c:init_special_inode; fs/stat.c:generic_fillattr@v6.18.46 -/
theorem devnull_regular_type_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 4 4096 fstat_input fstat_kinds_model
        (Ok (mkEffect 0 [(4096, devnull_as_regular)] []) m' evs) := by
  sys_refute

/-- A zero `st_rdev` is refused: `i_rdev` is 1:3, encoded 259.
kernel: include/linux/kdev_t.h:new_encode_dev,MKDEV; fs/stat.c:cp_new_stat@v6.18.46 -/
theorem devnull_zero_rdev_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 4 4096 fstat_input fstat_kinds_model
        (Ok (mkEffect 0 [(4096, devnull_zero_rdev)] []) m' evs) := by
  sys_refute

/-- A nonzero `st_size` is refused: nothing ever resized the node.
kernel: drivers/char/mem.c:write_null; fs/stat.c:generic_fillattr@v6.18.46 -/
theorem devnull_nonzero_size_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 4 4096 fstat_input fstat_kinds_model
        (Ok (mkEffect 0 [(4096, devnull_sized)] []) m' evs) := by
  sys_refute

/-- …and so is a nonzero `st_blocks`: `i_blocks` is what `mknod` left as
well (`generic_fillattr`, fs/stat.c:106, v6.18.46).
kernel: drivers/char/mem.c:write_null; fs/stat.c:generic_fillattr@v6.18.46 -/
theorem devnull_nonzero_blocks_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 4 4096 fstat_input fstat_kinds_model
        (Ok (mkEffect 0 [(4096, devnull_blocks)] []) m' evs) := by
  sys_refute

/-- `access_ok` refuses the range on the device arm exactly as on the file
arm: `cp_new_stat` (fs/stat.c:506, v6.18.46) hands the range to copy_to_user on the same line.
kernel: fs/stat.c:cp_new_stat; include/linux/uaccess.h:_inline_copy_to_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem devnull_access_ok_fault (i : SyscallInput) (o : outcome SyscallEffect) :
    fstat_spec 4 (Z_to_bv 64 (2 ^ 63)) i fstat_kinds_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) fstat_kinds_model [] := by
  sys_norm

/-- …and a landing zone one byte shy is declined on the device arm too.
kernel: include/linux/uaccess.h:_inline_copy_to_user; fs/stat.c:cp_new_stat@v6.18.46 -/
theorem devnull_one_byte_short_is_unmodeled (o : outcome SyscallEffect) :
    fstat_spec 4 4096 fstat_input_short fstat_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- THE BOUNDARY OF `access_ok` ON THE DEVICE ARM, which has its own
`access_okb` call: a 128-byte range ending exactly at the limit is
admitted by `__access_ok` (include/asm-generic/access_ok.h:40, v6.18.46)
and the walk then decides — the fixture memory does not back it, so the
arm declines…
kernel: include/asm-generic/access_ok.h:__access_ok; include/linux/uaccess.h:_inline_copy_to_user; fs/stat.c:cp_new_stat@v6.18.46 -/
theorem devnull_access_ok_last_zone_is_walked (o : outcome SyscallEffect) :
    fstat_spec 4 (Z_to_bv 64 (2 ^ 47 - 128)) fstat_input fstat_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and one byte higher the range crosses the limit: -EFAULT before a
byte moves, on any memory.
kernel: include/asm-generic/access_ok.h:__access_ok; include/linux/uaccess.h:_inline_copy_to_user; fs/stat.c:cp_new_stat@v6.18.46 -/
theorem devnull_access_ok_past_the_limit_faults (i : SyscallInput) (o : outcome SyscallEffect) :
    fstat_spec 4 (Z_to_bv 64 (2 ^ 47 - 127)) i fstat_kinds_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) fstat_kinds_model [] := by
  sys_norm

/-- THE RECEPTIVENESS GUARD on the device arm, first half: a pin that is
well-formed but not the device's — a regular file's record under
`devnull_path` — is declined.  No run builds one; the guard is what keeps
the `choose` below it satisfiable, since nothing is both `stat_devnull_ok`
and stable-equal to a record that is not.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem devnull_file_shaped_pin_is_declined (o : outcome SyscallEffect) :
    fstat_spec 4 4096 fstat_input fstat_kinds_model_badpin_file o ↔ o = Unmodeled := by
  sys_norm

/-- …second half: a pin that satisfies the device's assertions but is not
128 bytes wide is declined as well — the two predicates are tested
together, and dropping either would let through a delivery from a record
`cp_new_stat` never wrote.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem devnull_short_pin_is_declined (o : outcome SyscallEffect) :
    fstat_spec 4 4096 fstat_input fstat_kinds_model_badpin_short o ↔ o = Unmodeled := by
  sys_norm

/-- THE ADMITTED SET on the pinned device: the assertions and the pin's
stable members, the model unchanged.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat,generic_fillattr; fs/inode.c:init_special_inode@v6.18.46 -/
theorem devnull_pinned_stat_iff (o : outcome SyscallEffect) :
    fstat_spec 4 4096 fstat_input fstat_kinds_model_pinned o
      ↔ ∃ bs : List byte,
          o = Ok (mkEffect 0 [(4096, bs)] []) fstat_kinds_model_pinned []
          ∧ stat_buf_wf bs = true ∧ stat_devnull_ok bs = true
          ∧ stat_stable_eqb bs devnull_truthful = true := by
  sys_norm

/-- New timestamps against the pinned device are admitted…
kernel: include/uapi/linux/stat.h:S_IFCHR; fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem devnull_pinned_new_times_admitted :
    fstat_spec 4 4096 fstat_input fstat_kinds_model_pinned
      (Ok (mkEffect 0 [(4096, devnull_new_times)] [])
          fstat_kinds_model_pinned []) := by
  rw [devnull_pinned_stat_iff]
  exact ⟨devnull_new_times, rfl, wf_devnull_new_times, ok_devnull_new_times, stable_devnull_new_times⟩

/-- …and a different inode is not: the node keeps its identity.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem devnull_pinned_inode_defector_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 4 4096 fstat_input fstat_kinds_model_pinned
        (Ok (mkEffect 0 [(4096, devnull_other_inode)] []) m' evs) := by
  sys_refute

/-- THE OTHER DEVICE'S RECORD is refused for the null device: the random
device's `st_rdev` is 1:9, encoded 265, and /dev/null's is 259.
kernel: include/linux/kdev_t.h:new_encode_dev,MKDEV; drivers/char/mem.c:memory_open; fs/stat.c:cp_new_stat@v6.18.46 -/
theorem devnull_urandom_record_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 4 4096 fstat_input fstat_kinds_model
        (Ok (mkEffect 0 [(4096, urandom_truthful)] []) m' evs) := by
  sys_refute

/-! ## fstat: /dev/urandom, the other device the model knows

The same inode members as /dev/null, set by `init_special_inode`
(fs/inode.c:2552-2577, v6.18.46), read back by `generic_fillattr`
(fs/stat.c:82-113, v6.18.46) and delivered by `cp_new_stat`
(fs/stat.c:470-507), and the node is minor 9 of
major 1: `memory_open` (drivers/char/mem.c:707-727, v6.18.46) installs
the `urandom` entry of its table for minor 9 (:701), so `st_rdev` is
`new_encode_dev` (include/linux/kdev_t.h:39-44) of `MKDEV(1, 9)` (:12),
which is 265.  A write to the device is `random_write_iter`
(drivers/char/random.c:1448-1451, v6.18.46) and mixes into the pool
(`write_pool_user`, :1420-1446) without touching the inode, so `st_size`
and `st_blocks` are the zero `mknod` left.  The pin is keyed under
`urandom_path`, so the two devices' pins are independent. -/

/-- THE ADMITTED SET for /dev/urandom on first stat: well-formed bytes
satisfying the device's assertions, recorded under `urandom_path`.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat,generic_fillattr; fs/inode.c:init_special_inode@v6.18.46 -/
theorem urandom_first_stat_iff (o : outcome SyscallEffect) :
    fstat_spec 8 4096 fstat_input fstat_kinds_model o
      ↔ ∃ bs : List byte,
          o = Ok (mkEffect 0 [(4096, bs)] []) (with_statpin urandom_path bs fstat_kinds_model) []
          ∧ stat_buf_wf bs = true ∧ stat_urandom_ok bs = true := by
  sys_norm

/-- S_IFCHR, `st_rdev` 265, zero size and blocks: admitted, and pinned.
kernel: include/uapi/linux/stat.h:S_IFCHR; include/linux/kdev_t.h:new_encode_dev,MKDEV; drivers/char/mem.c:memory_open; drivers/char/random.c:random_write_iter,write_pool_user@v6.18.46 -/
theorem urandom_answer_admitted :
    fstat_spec 8 4096 fstat_input fstat_kinds_model
      (Ok (mkEffect 0 [(4096, urandom_truthful)] [])
          (with_statpin urandom_path urandom_truthful fstat_kinds_model) []) := by
  rw [urandom_first_stat_iff]
  exact ⟨urandom_truthful, rfl, wf_urandom, ok_urandom⟩

/-- A REGULAR-FILE type for the random device is refused: `init_special_inode`
gave the node S_IFCHR.
kernel: fs/inode.c:init_special_inode; fs/stat.c:generic_fillattr@v6.18.46 -/
theorem urandom_regular_type_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 8 4096 fstat_input fstat_kinds_model
        (Ok (mkEffect 0 [(4096, urandom_as_regular)] []) m' evs) := by
  sys_refute

/-- THE NULL DEVICE'S RECORD is refused for the random device: a kernel
that confused the two nodes would deliver `st_rdev` 259 where minor 9
encodes to 265.
kernel: include/linux/kdev_t.h:new_encode_dev,MKDEV; drivers/char/mem.c:memory_open; fs/stat.c:cp_new_stat@v6.18.46 -/
theorem urandom_devnull_record_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 8 4096 fstat_input fstat_kinds_model
        (Ok (mkEffect 0 [(4096, devnull_truthful)] []) m' evs) := by
  sys_refute

/-- A nonzero `st_size` is refused: nothing ever resized the node.
kernel: drivers/char/random.c:random_write_iter,write_pool_user; fs/stat.c:generic_fillattr@v6.18.46 -/
theorem urandom_nonzero_size_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 8 4096 fstat_input fstat_kinds_model
        (Ok (mkEffect 0 [(4096, urandom_sized)] []) m' evs) := by
  sys_refute

/-- …and so is a nonzero `st_blocks` (`generic_fillattr`, fs/stat.c:106,
v6.18.46, off a node nothing ever grew).
kernel: drivers/char/random.c:random_write_iter,write_pool_user; fs/stat.c:generic_fillattr@v6.18.46 -/
theorem urandom_nonzero_blocks_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 8 4096 fstat_input fstat_kinds_model
        (Ok (mkEffect 0 [(4096, urandom_blocks)] []) m' evs) := by
  sys_refute

/-- `access_ok` refuses the range on the random device's arm exactly as on
the null device's: one `cp_new_stat` (fs/stat.c:506, v6.18.46) serves both.
kernel: fs/stat.c:cp_new_stat; include/linux/uaccess.h:_inline_copy_to_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem urandom_access_ok_fault (i : SyscallInput) (o : outcome SyscallEffect) :
    fstat_spec 8 (Z_to_bv 64 (2 ^ 63)) i fstat_kinds_model o
      ↔ o = Ok (mkEffect (errno_ret EFAULT) [] []) fstat_kinds_model [] := by
  sys_norm

/-- …and a landing zone one byte shy is declined on this arm too.
kernel: include/linux/uaccess.h:_inline_copy_to_user; fs/stat.c:cp_new_stat@v6.18.46 -/
theorem urandom_one_byte_short_is_unmodeled (o : outcome SyscallEffect) :
    fstat_spec 8 4096 fstat_input_short fstat_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- THE RECEPTIVENESS GUARD on the random device's arm: a pin that is
well-formed, a character device, and the OTHER device's — the null
device's record under `urandom_path` — is declined.  No run builds one;
the guard is what keeps the `choose` below it satisfiable, since nothing
is both `stat_urandom_ok` and stable-equal to a record whose `st_rdev` is
259.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem urandom_other_device_pin_is_declined (o : outcome SyscallEffect) :
    fstat_spec 8 4096 fstat_input fstat_kinds_model_urandom_badpin_devnull o ↔ o = Unmodeled := by
  sys_norm

/-- THE ADMITTED SET on the pinned random device: the assertions and the
pin's stable members, the model unchanged.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat,generic_fillattr; fs/inode.c:init_special_inode@v6.18.46 -/
theorem urandom_pinned_stat_iff (o : outcome SyscallEffect) :
    fstat_spec 8 4096 fstat_input fstat_kinds_model_urandom_pinned o
      ↔ ∃ bs : List byte,
          o = Ok (mkEffect 0 [(4096, bs)] []) fstat_kinds_model_urandom_pinned []
          ∧ stat_buf_wf bs = true ∧ stat_urandom_ok bs = true
          ∧ stat_stable_eqb bs urandom_truthful = true := by
  sys_norm

/-- New timestamps against the pinned random device are admitted…
kernel: include/uapi/linux/stat.h:S_IFCHR; fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem urandom_pinned_new_times_admitted :
    fstat_spec 8 4096 fstat_input fstat_kinds_model_urandom_pinned
      (Ok (mkEffect 0 [(4096, urandom_new_times)] [])
          fstat_kinds_model_urandom_pinned []) := by
  rw [urandom_pinned_stat_iff]
  exact ⟨urandom_new_times, rfl, wf_urandom_new_times, ok_urandom_new_times, stable_urandom_new_times⟩

/-- …and a different inode is not: the node keeps its identity.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem urandom_pinned_inode_defector_rejected (m' : Model) (evs : List event) :
    ¬ fstat_spec 8 4096 fstat_input fstat_kinds_model_urandom_pinned
        (Ok (mkEffect 0 [(4096, urandom_other_inode)] []) m' evs) := by
  sys_refute

/-- THE TWO PINS ARE INDEPENDENT: with /dev/null already pinned, the first
stat of /dev/urandom is still a first stat — its admitted set is the
unpinned one, and it records its own bytes under `urandom_path` beside the
null device's, not over them.  Two nodes, two inodes (`generic_fillattr`
reads each node's own `i_ino`, fs/stat.c:89, v6.18.46).
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat,generic_fillattr; fs/inode.c:init_special_inode@v6.18.46 -/
theorem urandom_first_stat_beside_devnull_pin_iff (o : outcome SyscallEffect) :
    fstat_spec 8 4096 fstat_input fstat_kinds_model_pinned o
      ↔ ∃ bs : List byte,
          o = Ok (mkEffect 0 [(4096, bs)] []) (with_statpin urandom_path bs fstat_kinds_model_pinned) []
          ∧ stat_buf_wf bs = true ∧ stat_urandom_ok bs = true := by
  sys_norm

/-! ## The dispatcher: syscall 80 and the `unsigned int fd` truncation

`__NR3264_fstat` is 80 (include/uapi/asm-generic/unistd.h:212-213, v6.18.46;
`80 64 fstat sys_newfstat` in scripts/syscall.tbl:104).  `fd` is
`unsigned int` (fs/stat.c:550), narrowed by `__SYSCALL_DEFINEx`
(arch/riscv/include/asm/syscall_wrapper.h:82-88) through `__SC_CAST`
(include/linux/syscalls.h:132, v6.18.46): a register of `2^32 + k` is fd `k`, so the
truncation ALIASES rather than rejects. -/

/-- Syscall 80 on a closed fd reaches the arm and answers -EBADF.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_fstat; fs/stat.c:newfstat,vfs_fstat@v6.18.46 -/
theorem sysno_80_is_fstat (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 80 [9, 4096, 0, 0, 0, 0] (fun _ => none) stat_out) fstat_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) fstat_model [] := by
  sys_norm

/-- An unopened number `| 2^32` is still -EBADF: truncation does not
invent live fds (the probe's `HI + 12345`).
probe: testing/syscall-check/tests/fstat_spec.c#conform -- trunc-dead -/
theorem trunc_dead_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (fstat_call (Z_to_bv 64 (2 ^ 32 + 12345)) 4096 stat_out) fstat_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) fstat_model [] := by
  sys_norm

/-- …and does not let it succeed.
probe: testing/syscall-check/tests/fstat_spec.c#reject --mutate fstat:ret=0 -- trunc-dead -/
theorem trunc_dead_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fstat_call (Z_to_bv 64 (2 ^ 32 + 12345)) 4096 stat_out) fstat_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A register of all ones is fd -1 after the `unsigned int` cast, a
number no table holds: -EBADF, the probe's second `unopened` call.
probe: testing/syscall-check/tests/fstat_spec.c#conform -- unopened -/
theorem all_ones_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (fstat_call (Z_to_bv 64 (-1)) 4096 stat_out) fstat_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) fstat_model [] := by
  sys_norm

/-- …and does not succeed: the negative fd is the one the probe's first
call does not reach, mutated on its own.
probe: testing/syscall-check/tests/fstat_spec.c#reject --mutate fstat#2:ret=0 -- unopened -/
theorem all_ones_fd_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (fstat_call (Z_to_bv 64 (-1)) 4096 stat_out) fstat_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- `3 | 2^32` IS fd 3, and is answered with the file's admitted set.
probe: testing/syscall-check/tests/fstat_spec.c#conform -- trunc-live -/
theorem trunc_live_is_the_file (o : outcome SyscallEffect) :
    syscall_spec (fstat_call (Z_to_bv 64 (2 ^ 32 + 3)) 4096 stat_out) fstat_model o
      ↔ ∃ bs : List byte,
          o = Ok (mkEffect 0 [(4096, bs)] []) (with_statpin fstat_path bs fstat_model) []
          ∧ stat_buf_wf bs = true ∧ stat_size_ok 9 bs = true := by
  sys_norm

/-- A register of exactly `2^32` is fd 0, a live channel: declined, not
-EBADF.
probe: testing/syscall-check/tests/fstat_spec.c#fail-closed --expect-unmodeled fstat -- trunc-zero -/
theorem trunc_zero_is_the_channel (o : outcome SyscallEffect) :
    syscall_spec (fstat_call (Z_to_bv 64 (2 ^ 32)) 4096 stat_out) fstat_kinds_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …so the -EBADF a model comparing the full register would give is refused.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_fstat; fs/stat.c:newfstat,vfs_fstat; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem trunc_zero_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 80 [Z_to_bv 64 (2 ^ 32), 4096, 0, 0, 0, 0] (fun _ => none) stat_out)
        fstat_kinds_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-! ## A17: FdFileRW and FdFileA -/

def a17_stat_model : Model :=
  fixture_of (fds := [(3, .FdFileRW [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_stat_model.eq_1

/-- `fstat` through a read-write file declines (`Sys/Fs/Stat.lean`'s
header declares the narrowing).  The same call on an `FdFile` answers
-EFAULT at the buffer past `TASK_SIZE` (`vfs_fstat`, fs/stat.c, Linux
v6.18.46, fills the kstat that the copy-out then fails on), so a mutant
answering this kind as `FdFile` fails here.
kernel: fs/stat.c:vfs_fstat@v6.18.46 -/
theorem a17_rdwr_fstat_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 80 [3, Z_to_bv 64 TASK_SIZE, 0, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_stat_model o ↔ o = Unmodeled := by
  sys_norm

def a17_stat_append_model : Model :=
  fixture_of (fds := [(3, .FdFileA [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_stat_append_model.eq_1

/-- `fstat` through an append-mode file declines (`Sys/Fs/Stat.lean`'s
header declares the narrowing).  The same call on an `FdFileW` answers
-EFAULT at the buffer past `TASK_SIZE` (`vfs_fstat`, fs/stat.c, Linux
v6.18.46, fills the kstat that the copy-out then fails on), so a mutant
answering this kind as `FdFileW` fails here.
kernel: fs/stat.c:vfs_fstat@v6.18.46 -/
theorem a17_append_fstat_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 80 [3, Z_to_bv 64 TASK_SIZE, 0, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_stat_append_model o ↔ o = Unmodeled := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Stat
