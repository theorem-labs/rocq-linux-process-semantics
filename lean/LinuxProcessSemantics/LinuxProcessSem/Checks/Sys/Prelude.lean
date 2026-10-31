import Lean
import LinuxProcessSemantics.LinuxProcessSem.Specs

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Prelude — the checkers' shared helpers, reflections and tactics

Mirrors `theories/LinuxProcessSem/Checks/Sys/Prelude.v`: the
infrastructure every executable checker under `Checks/Sys/` shares.  It
mirrors no kernel source and holds nothing syscall-specific; the
arguments for each definition are on its Rocq twin and are not repeated
here.  Not part of the trusted specification: a checker's proofs relate
it to the relational spec in the matching `Sys` module, and those proofs
are what carry the trust.

Every top-level Rocq definition and every lemma is here under its own
name — `write_source_prefix`, `gather_prefix_full` and
`gather_iovecs_length` last, once `Uaccess.write_source`,
`State.rw_count_clamp`, `State.gather_iovecs`, `State.gather_prefix` and
`State.iovs_total` had landed — and `sys_unfold`'s list is Rocq's list
in full.  That list is the one place this file depends on a name outside
`Monad`, `Sys.Syscall` and `Sys.Fs.File`, and it is worth saying how it
got there:

- `sys_unfold` can only unfold a name the Lean tree defines, so each of
  Rocq's entries joined the macro when its twin landed — `lowest_fd`
  (`Sys/Fs/File.lean`), `set_urandom` (`Monad.lean`) and, last,
  `set_sigmask_deliver` (`Sys/Kernel/Signal.lean`), which the macro
  reaches through `Specs`.  A Rocq entry the tree still lacked would make
  the macro narrower than its twin, and the Cases file's `sys_unfold`
  section holds one example per non-`Monad` sugar so that a missing entry
  fails there rather than in the first checker proof to meet it.  The
  header's baseline is a71fd38a, the squash that landed the 2026-09-11
  work on main (#794): its `Prelude.v` is byte-identical to the
  day-branch commit this file was read at (2b5fb827, which descends from
  no history main has), and it differs from the port's common baseline
  f44244ad in exactly that `set_urandom` entry of `sys_unfold`, which
  `openat`'s `/dev/urandom` change (#712) added; no definition or lemma
  moved.

Spellings that differ from Rocq without changing a value, said once:
Rocq's `firstn`/`skipn` are `List.take`/`List.drop`; `existsb`/`forallb`
are `List.any`/`List.all`; `In` is `∈`; `Nat.eqb` is `==` on `Nat`;
`Z.leb`/`Z.ltb`/`Z.eqb` are the decidable `≤`/`<`/`=` on `Int`; `negb`
is `!`.  The tactics `srw`, `hrw`, `hall`, `bool_true`, `inv_ok` and
`sys_unfold` are macros — `inv_ok` over two small elaborators, because
its arms select a hypothesis by shape, which a macro cannot — and each
one's docstring says how its Lean arms correspond to Rocq's. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

/-- The three answers a checker gives: the effect is admitted (with the
post-model and the events the spec chose), the effect is one the spec
refuses, or the call is outside the modeled surface.  Rocq:
`Prelude.check_result`. -/
inductive check_result : Type
  | CheckOk (m : Model) (evs : List event)
  | CheckReject
  | CheckUnmodeled

export check_result (CheckOk CheckReject CheckUnmodeled)

/-! ## Boolean helpers and their reflections -/

theorem bv_eqb_refl {n : Nat} (a : BitVec n) : bv_eqb a a = true :=
  (bv_eqb_eq a a).mpr rfl

/-- Byte-list equality; bytes are `bv 8`. -/
def listN_eqb : List byte → List byte → Bool
  | [], [] => true
  | a :: r1, b :: r2 => bv_eqb a b && listN_eqb r1 r2
  | _, _ => false

theorem listN_eqb_eq (l1 l2 : List byte) : listN_eqb l1 l2 = true ↔ l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons b r2 =>
      simp only [listN_eqb, Bool.false_eq_true, reduceCtorEq]
  | cons a r1 ih =>
    cases l2 with
    | nil => simp only [listN_eqb, Bool.false_eq_true, reduceCtorEq]
    | cons b r2 =>
      simp only [listN_eqb, Bool.and_eq_true, bv_eqb_eq, ih, List.cons.injEq]

/-- Equality of zero-range / unmap-range lists (`eff_zeros`,
`eff_unmaps`). -/
def listNN_eqb : List (word × word) → List (word × word) → Bool
  | [], [] => true
  | (a1, n1) :: r1, (a2, n2) :: r2 =>
      bv_eqb a1 a2 && bv_eqb n1 n2 && listNN_eqb r1 r2
  | _, _ => false

theorem listNN_eqb_eq (l1 l2 : List (word × word)) : listNN_eqb l1 l2 = true ↔ l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons p r2 =>
      obtain ⟨a2, n2⟩ := p
      simp only [listNN_eqb, Bool.false_eq_true, reduceCtorEq]
  | cons p r1 ih =>
    obtain ⟨a1, n1⟩ := p
    cases l2 with
    | nil => simp only [listNN_eqb, Bool.false_eq_true, reduceCtorEq]
    | cons q r2 =>
      obtain ⟨a2, n2⟩ := q
      simp only [listNN_eqb, Bool.and_eq_true, bv_eqb_eq, ih, List.cons.injEq, Prod.mk.injEq,
        and_assoc]

/-- Equality for the symbolic pre-effect copy ledger. -/
def copy_eqb (c1 c2 : MemCopy) : Bool :=
  bv_eqb c1.copy_src c2.copy_src
  && bv_eqb c1.copy_dst c2.copy_dst
  && bv_eqb c1.copy_len c2.copy_len

def listCopy_eqb : List MemCopy → List MemCopy → Bool
  | [], [] => true
  | c1 :: r1, c2 :: r2 => copy_eqb c1 c2 && listCopy_eqb r1 r2
  | _, _ => false

theorem copy_eqb_eq (c1 c2 : MemCopy) : copy_eqb c1 c2 = true ↔ c1 = c2 := by
  obtain ⟨s1, d1, n1⟩ := c1
  obtain ⟨s2, d2, n2⟩ := c2
  simp only [copy_eqb, Bool.and_eq_true, bv_eqb_eq, MemCopy.mkCopy.injEq, and_assoc]

theorem listCopy_eqb_eq (l1 l2 : List MemCopy) : listCopy_eqb l1 l2 = true ↔ l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons c2 r2 => simp only [listCopy_eqb, Bool.false_eq_true, reduceCtorEq]
  | cons c1 r1 ih =>
    cases l2 with
    | nil => simp only [listCopy_eqb, Bool.false_eq_true, reduceCtorEq]
    | cons c2 r2 =>
      simp only [listCopy_eqb, Bool.and_eq_true, copy_eqb_eq, ih, List.cons.injEq]

/-- Equality for syscall write lists: addresses plus their byte strings. -/
def writes_eqb : List (word × List byte) → List (word × List byte) → Bool
  | [], [] => true
  | (a1, bs1) :: r1, (a2, bs2) :: r2 =>
      bv_eqb a1 a2 && listN_eqb bs1 bs2 && writes_eqb r1 r2
  | _, _ => false

theorem writes_eqb_eq (l1 l2 : List (word × List byte)) : writes_eqb l1 l2 = true ↔ l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons p r2 =>
      obtain ⟨a2, bs2⟩ := p
      simp only [writes_eqb, Bool.false_eq_true, reduceCtorEq]
  | cons p r1 ih =>
    obtain ⟨a1, bs1⟩ := p
    cases l2 with
    | nil => simp only [writes_eqb, Bool.false_eq_true, reduceCtorEq]
    | cons q r2 =>
      obtain ⟨a2, bs2⟩ := q
      simp only [writes_eqb, Bool.and_eq_true, bv_eqb_eq, listN_eqb_eq, ih, List.cons.injEq,
        Prod.mk.injEq, and_assoc]

/-! ## Errno returns -/

/-- Range of a 64-bit word's unsigned value, with the modulus exposed as
the `two_pow_64` constant. -/
theorem word_unsigned_range (w : word) : 0 ≤ bv_unsigned w ∧ bv_unsigned w < two_pow_64 := by
  unfold bv_unsigned two_pow_64
  have h := w.isLt
  omega

/-- The unsigned value of an in-range errno return. -/
theorem errno_ret_unsigned (e : Int) (h1 : 1 ≤ e) (h2 : e ≤ 4095) :
    bv_unsigned (errno_ret e) = two_pow_64 - e := by
  unfold errno_ret Z_to_bv bv_unsigned two_pow_64
  rw [BitVec.toNat_ofInt]
  have hmod : (-e) % ((2 ^ 64 : Nat) : Int) = 2 ^ 64 - e := by omega
  rw [hmod]
  omega

/-- An error-encoded return value is exactly `errno_ret e` for an errno in
`[1, 4095]`. -/
theorem errno_ret_error_b (e : Int) (h1 : 1 ≤ e) (h2 : e ≤ 4095) :
    addr_is_error_b (errno_ret e) = true := by
  unfold addr_is_error_b
  rw [errno_ret_unsigned e h1 h2]
  unfold two_pow_64
  exact decide_eq_true (by omega)

theorem addr_is_error_b_errno (r : word) (h : addr_is_error_b r = true) :
    ∃ e, 1 ≤ e ∧ e ≤ 4095 ∧ r = errno_ret e := by
  unfold addr_is_error_b at h
  rw [decide_eq_true_eq] at h
  have hr := word_unsigned_range r
  refine ⟨2 ^ 64 - bv_unsigned r, ?_, ?_, ?_⟩
  · unfold two_pow_64 at hr; omega
  · unfold two_pow_64 at h; omega
  · apply BitVec.eq_of_toNat_eq
    have hu := errno_ret_unsigned (2 ^ 64 - bv_unsigned r)
      (by unfold two_pow_64 at hr; omega) (by unfold two_pow_64 at h; omega)
    unfold bv_unsigned two_pow_64 at hu h hr
    unfold bv_unsigned
    omega

/-- Does `r` encode `-e` for some errno in the injectable set `es`? -/
def errno_ret_in (es : List Int) (r : word) : Bool :=
  es.any (fun e => bv_eqb r (errno_ret e))

theorem errno_ret_in_true (es : List Int) (r : word) :
    errno_ret_in es r = true ↔ ∃ e, e ∈ es ∧ r = errno_ret e := by
  simp only [errno_ret_in, List.any_eq_true, bv_eqb_eq]

theorem errno_ret_in_intro (es : List Int) (e : Int) (h : e ∈ es) :
    errno_ret_in es (errno_ret e) = true :=
  (errno_ret_in_true es (errno_ret e)).mpr ⟨e, h, rfl⟩

/-- Every injectable set draws from the error-return window `[1, 4095]`.
The top is `MAX_ERRNO`, not the largest errno Linux defines, so this is
the band `IS_ERR_VALUE` reserves rather than an errno set: it is
deliberately wider, so that every implementation's errno choice lies
inside it.  Why that window is the one a riscv64 return is read against
is on the `Checks/Cases` twin's `ErrnoWindow` section. -/
def errnos_ok (es : List Int) : Bool :=
  es.all (fun e => decide (1 ≤ e) && decide (e ≤ 4095))

theorem errnos_ok_range (es : List Int) (e : Int) (hok : errnos_ok es = true) (he : e ∈ es) :
    1 ≤ e ∧ e ≤ 4095 := by
  simp only [errnos_ok, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact hok e he

/-- A value far below the error-encoding window (in particular any
fd < 2^31, or any grant address below `alloc_top`) never matches an
injectable errno. -/
theorem errno_ret_in_below (es : List Int) (r : word) (hok : errnos_ok es = true)
    (hr : bv_unsigned r ≤ two_pow_64 - 4096) : errno_ret_in es r = false := by
  simp only [errno_ret_in, List.any_eq_false, bv_eqb, beq_iff_eq]
  intro e he heq
  obtain ⟨h1, h2⟩ := errnos_ok_range es e hok he
  rw [heq, errno_ret_unsigned e h1 h2] at hr
  omega

theorem errno_ret_in_fd (es : List Int) (fd : word) (hok : errnos_ok es = true)
    (hfd : bv_unsigned fd < 2 ^ 31) : errno_ret_in es fd = false := by
  apply errno_ret_in_below es fd hok
  unfold two_pow_64
  omega

/-! ## Writable ranges -/

/-- Is `[buf, buf+n)` writable-mapped?  Decides the delivered-prefix
writability side condition of `read_spec`. -/
def wmem_ok (i : SyscallInput) (buf n : word) : Bool :=
  match read_bytes_map i.in_wmem buf n with
  | some _ => true
  | none => false

theorem wmem_ok_true (i : SyscallInput) (buf n : word) :
    wmem_ok i buf n = true ↔ read_bytes_map i.in_wmem buf n ≠ none := by
  unfold wmem_ok
  cases read_bytes_map i.in_wmem buf n with
  | none => simp only [Bool.false_eq_true, ne_eq, not_true_eq_false]
  | some w => simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-- A prefix of a readable range is readable (and reads the prefix). -/
theorem read_bytes_aux_prefix (k n : Nat) (mp : word → Option byte) (a : word) (w : List byte)
    (hk : k ≤ n) (hw : read_bytes_aux mp a n = some w) :
    read_bytes_aux mp a k = some (w.take k) := by
  induction k generalizing n a w with
  | zero => rfl
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [read_bytes_aux] at hw
      cases hb : mp a with
      | none => rw [hb] at hw; exact absurd hw (by simp only [reduceCtorEq, not_false_eq_true])
      | some b =>
        rw [hb] at hw
        cases hr : read_bytes_aux mp (a + 1) n with
        | none => rw [hr] at hw; exact absurd hw (by simp only [reduceCtorEq, not_false_eq_true])
        | some r =>
          rw [hr] at hw
          simp only [Option.some.injEq] at hw
          subst hw
          simp only [read_bytes_aux, hb, ih n (a + 1) r (by omega) hr, List.take_succ_cons]

theorem read_bytes_map_prefix (mp : word → Option byte) (a len k : word) (w : List byte)
    (hk : bv_unsigned k ≤ bv_unsigned len) (hw : read_bytes_map mp a len = some w) :
    read_bytes_map mp a k = some (w.take (word_to_nat k)) := by
  rw [read_bytes_map_eq] at hw ⊢
  apply read_bytes_aux_prefix (word_to_nat k) (word_to_nat len) mp a w _ hw
  unfold bv_unsigned at hk
  unfold word_to_nat
  omega

/-- Full-range writability implies prefix writability — lets callers that
established the whole `count` writable keep working. -/
theorem wmem_ok_of_full (i : SyscallInput) (buf count : word) (w : List byte) (k : word)
    (hw : read_bytes_map i.in_wmem buf count = some w)
    (hk : bv_unsigned k ≤ bv_unsigned count) : wmem_ok i buf k = true := by
  unfold wmem_ok
  rw [read_bytes_map_prefix i.in_wmem buf count k w hk hw]

/-- Full-readability facts: when the whole range reads, the readable
prefix IS the whole buffer, of the full length. -/
theorem read_bytes_aux_length (mp : word → Option byte) (k : Nat) (a : word) (w : List byte)
    (hw : read_bytes_aux mp a k = some w) : w.length = k := by
  induction k generalizing a w with
  | zero =>
    simp only [read_bytes_aux, Option.some.injEq] at hw
    subst hw
    rfl
  | succ k ih =>
    simp only [read_bytes_aux] at hw
    cases hb : mp a with
    | none => rw [hb] at hw; exact absurd hw (by simp only [reduceCtorEq, not_false_eq_true])
    | some b =>
      rw [hb] at hw
      cases hr : read_bytes_aux mp (a + 1) k with
      | none => rw [hr] at hw; exact absurd hw (by simp only [reduceCtorEq, not_false_eq_true])
      | some r =>
        rw [hr] at hw
        simp only [Option.some.injEq] at hw
        subst hw
        simp only [List.length_cons, ih (a + 1) r hr]

theorem read_bytes_map_length (mp : word → Option byte) (a len : word) (w : List byte)
    (hw : read_bytes_map mp a len = some w) : (w.length : Int) = bv_unsigned len := by
  rw [read_bytes_map_eq] at hw
  rw [read_bytes_aux_length mp (word_to_nat len) a w hw]
  rfl

theorem readable_bytes_aux_full (mp : word → Option byte) (k : Nat) (a : word) (w : List byte)
    (hw : read_bytes_aux mp a k = some w) : readable_bytes_aux mp a k = w := by
  induction k generalizing a w with
  | zero =>
    simp only [read_bytes_aux, Option.some.injEq] at hw
    subst hw
    rfl
  | succ k ih =>
    simp only [read_bytes_aux] at hw
    cases hb : mp a with
    | none => rw [hb] at hw; exact absurd hw (by simp only [reduceCtorEq, not_false_eq_true])
    | some b =>
      rw [hb] at hw
      cases hr : read_bytes_aux mp (a + 1) k with
      | none => rw [hr] at hw; exact absurd hw (by simp only [reduceCtorEq, not_false_eq_true])
      | some r =>
        rw [hr] at hw
        simp only [Option.some.injEq] at hw
        subst hw
        simp only [readable_bytes_aux, hb, ih (a + 1) r hr]

theorem readable_bytes_full (mp : word → Option byte) (a len : word) (w : List byte)
    (hw : read_bytes_map mp a len = some w) : readable_bytes mp a len = w := by
  rw [read_bytes_map_eq] at hw
  rw [readable_bytes_eq]
  exact readable_bytes_aux_full mp (word_to_nat len) a w hw

/-- A SHORTER walk over a range that reads whole is that range's prefix.
What this is for — the `MAX_RW_COUNT` clamp on a write's source — is on
Rocq's `Prelude.readable_bytes_aux_prefix`; its consumer is
`write_source_prefix`, below. -/
theorem readable_bytes_aux_prefix (mp : word → Option byte) (n k : Nat) (a : word) (w : List byte)
    (hw : read_bytes_aux mp a n = some w) (hk : k ≤ n) :
    readable_bytes_aux mp a k = w.take k := by
  induction n generalizing k a w with
  | zero =>
    simp only [read_bytes_aux, Option.some.injEq] at hw
    subst hw
    cases k with
    | zero => rfl
    | succ k => omega
  | succ n ih =>
    simp only [read_bytes_aux] at hw
    cases hb : mp a with
    | none => rw [hb] at hw; exact absurd hw (by simp only [reduceCtorEq, not_false_eq_true])
    | some b =>
      rw [hb] at hw
      cases hr : read_bytes_aux mp (a + 1) n with
      | none => rw [hr] at hw; exact absurd hw (by simp only [reduceCtorEq, not_false_eq_true])
      | some r =>
        rw [hr] at hw
        simp only [Option.some.injEq] at hw
        subst hw
        cases k with
        | zero => rfl
        | succ k =>
          simp only [readable_bytes_aux, hb, List.take_succ_cons, ih k (a + 1) r hr (by omega)]

/-- A write's source is the clamped prefix of what its buffer holds:
`vfs_write` clamps `count` to `MAX_RW_COUNT` before the copy
(fs/read_write.c, `vfs_write`, v6.18.46), so on a buffer that reads
whole, `Uaccess.write_source` is the first `rw_count_clamp len` bytes of
the read.  Rocq's `firstn (Z.to_nat …)` is `List.take (…).toNat`. -/
theorem write_source_prefix (mp : word → Option byte) (a len : word) (w : List byte)
    (hw : read_bytes_map mp a len = some w) :
    Sys.Uaccess.write_source mp a len = w.take (rw_count_clamp len).toNat := by
  rw [read_bytes_map_eq] at hw
  unfold Sys.Uaccess.write_source
  rw [readable_bytes_eq]
  have hclamp : word_to_nat (Z_to_bv 64 (rw_count_clamp len)) = (rw_count_clamp len).toNat := by
    have hword := rw_count_clamp_word len
    unfold bv_unsigned at hword
    unfold word_to_nat
    omega
  rw [hclamp]
  apply readable_bytes_aux_prefix mp (word_to_nat len) _ a w hw
  unfold word_to_nat rw_count_clamp bv_unsigned
  omega

/-- A fully readable iovec sequence's gatherable prefix is the whole
flattening: `gather_prefix` stops at the first segment that reads short,
and when none does it is `gather_iovecs`'s answer. -/
theorem gather_prefix_full (mp : word → Option byte) (iovs : List (word × word))
    (bs : List byte) (hg : gather_iovecs mp iovs = some bs) : gather_prefix mp iovs = bs := by
  induction iovs generalizing bs with
  | nil =>
    simp only [gather_iovecs, Option.some.injEq] at hg
    subst hg
    rfl
  | cons iov r ih =>
    obtain ⟨base, len⟩ := iov
    simp only [gather_iovecs] at hg
    cases hb : read_bytes_map mp base len with
    | none => rw [hb] at hg; exact absurd hg (by simp only [reduceCtorEq, not_false_eq_true])
    | some b =>
      rw [hb] at hg
      cases hr : gather_iovecs mp r with
      | none => rw [hr] at hg; exact absurd hg (by simp only [reduceCtorEq, not_false_eq_true])
      | some rest =>
        rw [hr] at hg
        simp only [Option.some.injEq] at hg
        subst hg
        simp only [gather_prefix, readable_bytes_full mp base len b hb,
          read_bytes_map_length mp base len b hb, ↓reduceIte, ih rest hr]

/-- ...and it has the full requested length: every segment contributes
exactly its `iov_len`. -/
theorem gather_iovecs_length (mp : word → Option byte) (iovs : List (word × word))
    (bs : List byte) (hg : gather_iovecs mp iovs = some bs) :
    (bs.length : Int) = iovs_total iovs := by
  induction iovs generalizing bs with
  | nil =>
    simp only [gather_iovecs, Option.some.injEq] at hg
    subst hg
    rfl
  | cons iov r ih =>
    obtain ⟨base, len⟩ := iov
    simp only [gather_iovecs] at hg
    cases hb : read_bytes_map mp base len with
    | none => rw [hb] at hg; exact absurd hg (by simp only [reduceCtorEq, not_false_eq_true])
    | some b =>
      rw [hb] at hg
      cases hr : gather_iovecs mp r with
      | none => rw [hr] at hg; exact absurd hg (by simp only [reduceCtorEq, not_false_eq_true])
      | some rest =>
        rw [hr] at hg
        simp only [Option.some.injEq] at hg
        subst hg
        simp only [iovs_total, List.length_append, Int.natCast_add,
          read_bytes_map_length mp base len b hb, ih rest hr]

/-- A zero-length destination always reads: `read_spec`'s file branch can
only reach its unwritable case with a NONEMPTY delivered prefix. -/
theorem read_bytes_map_nil (mp : word → Option byte) (a : word) :
    read_bytes_map mp a (len_word ([] : List byte)) = some [] := by
  rw [read_bytes_map_eq]
  rfl

/-- The EFAULT gate is off when the readable prefix has the full
(arbitrary) length: it reduces to `!b && b`. -/
theorem negb_andb_diag (b : Bool) : (!b && b) = false := by
  cases b <;> rfl

/-! ## Return-only effects and the copy-in ledger -/

/-- Accept an effect that is exactly the return `r` and nothing else.
Why a successful open's return is never confused with an errno — the
`alloc_fd` scan is fuel-bounded at 4096 candidates — is on Rocq's
`Prelude.check_ret_only` and `State.alloc_fd`. -/
def check_ret_only (eff : SyscallEffect) (r : word) (m' : Model) (evs : List event)
    : check_result :=
  match eff with
  | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
      if bv_eqb ret r then CheckOk m' evs else CheckReject
  | _ => CheckReject

def access_ranges_eqb : List (word × Nat) → List (word × Nat) → Bool
  | [], [] => true
  | (a, n) :: xs', (b, k) :: ys' =>
      bv_eqb a b && (n == k) && access_ranges_eqb xs' ys'
  | _, _ => false

theorem access_ranges_eqb_eq (xs ys : List (word × Nat)) :
    access_ranges_eqb xs ys = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons p ys =>
      obtain ⟨b, k⟩ := p
      simp only [access_ranges_eqb, Bool.false_eq_true, reduceCtorEq]
  | cons p xs ih =>
    obtain ⟨a, n⟩ := p
    cases ys with
    | nil => simp only [access_ranges_eqb, Bool.false_eq_true, reduceCtorEq]
    | cons q ys =>
      obtain ⟨b, k⟩ := q
      simp only [access_ranges_eqb, Bool.and_eq_true, bv_eqb_eq, beq_iff_eq, ih, List.cons.injEq,
        Prod.mk.injEq, and_assoc]

theorem access_ranges_eqb_refl (xs : List (word × Nat)) : access_ranges_eqb xs xs = true :=
  (access_ranges_eqb_eq xs xs).mpr rfl

def clear_copyins (eff : SyscallEffect) : SyscallEffect :=
  with_copyins [] eff

def check_ret_only_copyins (reads : List (word × Nat)) (eff : SyscallEffect) (r : word)
    (m' : Model) (evs : List event) : check_result :=
  match check_ret_only (clear_copyins eff) r m' evs with
  | CheckOk m'' evs' =>
      if access_ranges_eqb eff.eff_copyins reads then CheckOk m'' evs' else CheckReject
  | result => result

def check_copyins (reads : List (word × Nat)) (eff : SyscallEffect) (result : check_result)
    : check_result :=
  if access_ranges_eqb eff.eff_copyins reads then result else CheckReject

def strip_copyin_prefix (reads : List (word × Nat)) (eff : SyscallEffect) : SyscallEffect :=
  with_copyins (eff.eff_copyins.drop reads.length) eff

def check_copyin_prefix (reads : List (word × Nat)) (eff : SyscallEffect) (result : check_result)
    : check_result :=
  match result with
  | CheckUnmodeled => CheckUnmodeled
  | result' =>
      if access_ranges_eqb (eff.eff_copyins.take reads.length) reads then result' else CheckReject

/-- Relate a spec that records one pathname read through `record_copyins`
to its checker: the body is decided against the effect with its ledger
CLEARED, then the claimed ledger must equal exactly that range, and
`CheckUnmodeled` passes straight through.  The consumers, and why the
pass-through is right, are on Rocq's `Prelude.check_copyins_after`. -/
def check_copyins_after (reads : List (word × Nat)) (eff : SyscallEffect) (result : check_result)
    : check_result :=
  match result with
  | CheckUnmodeled => CheckUnmodeled
  | result' => check_copyins reads eff result'

theorem check_copyins_after_ok_iff (reads : List (word × Nat)) (eff : SyscallEffect)
    (result : check_result) (m : Model) (evs : List event) :
    check_copyins_after reads eff result = CheckOk m evs ↔
    eff.eff_copyins = reads ∧ result = CheckOk m evs := by
  cases result with
  | CheckOk m' evs' =>
    simp only [check_copyins_after, check_copyins]
    cases hreads : access_ranges_eqb eff.eff_copyins reads with
    | true =>
      rw [access_ranges_eqb_eq] at hreads
      simp only [hreads, ↓reduceIte, true_and]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro heq
      rw [heq, access_ranges_eqb_refl] at hreads
      exact absurd hreads (by simp only [reduceCtorEq, not_false_eq_true])
  | CheckReject =>
    simp only [check_copyins_after, check_copyins]
    cases access_ranges_eqb eff.eff_copyins reads <;>
      simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, and_false]
  | CheckUnmodeled =>
    simp only [check_copyins_after, reduceCtorEq, and_false]

theorem check_copyins_after_unmodeled (reads : List (word × Nat)) (eff : SyscallEffect)
    (result : check_result) (h : check_copyins_after reads eff result = CheckUnmodeled) :
    result = CheckUnmodeled := by
  cases result with
  | CheckOk m evs =>
    simp only [check_copyins_after, check_copyins] at h
    cases hr : access_ranges_eqb eff.eff_copyins reads <;>
      simp only [hr, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | CheckReject =>
    simp only [check_copyins_after, check_copyins] at h
    cases hr : access_ranges_eqb eff.eff_copyins reads <;>
      simp only [hr, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | CheckUnmodeled => rfl

theorem record_copyins_clear_ok (reads : List (word × Nat)) (spec : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (hreads : eff.eff_copyins = reads) (hspec : spec i m (Ok (clear_copyins eff) m' evs)) :
    record_copyins reads spec i m (Ok eff m' evs) := by
  have h := record_copyins_ok_empty reads spec i m (clear_copyins eff) m' evs rfl hspec
  have heff : with_copyins reads (clear_copyins eff) = eff := by
    obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
    simp only [with_copyins, clear_copyins] at hreads ⊢
    rw [hreads]
  rw [heff] at h
  exact h

/-! ## Bind inversions

Each reads what `bind` admits at an `Ok` or an `Unmodeled` off a reader
that emits nothing (`input`, `get_model`) or off `record_copyins`. -/

theorem input_bind_ok_inv {A : Type} (k : SyscallInput → Sys A) (i : SyscallInput) (m : Model)
    (x : A) (m' : Model) (evs : List event) (h : bind input k i m (Ok x m' evs)) :
    k i i m (Ok x m' evs) := by
  obtain ⟨i', m1, evs1, evs2, hin, hk, hevs⟩ := h
  simp only [input, outcome.Ok.injEq] at hin
  obtain ⟨rfl, rfl, rfl⟩ := hin
  subst hevs
  exact hk

theorem record_copyins_ok_inv (reads : List (word × Nat)) (spec : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (h : record_copyins reads spec i m (Ok eff m' evs)) :
    ∃ core, spec i m (Ok core m' evs) ∧
      eff = with_copyins (reads ++ core.eff_copyins) core := by
  obtain ⟨core, m1, evs1, evs2, hcore, hpure, hevs⟩ := h
  simp only [Monad.pure, outcome.Ok.injEq] at hpure
  obtain ⟨rfl, rfl, rfl⟩ := hpure
  rw [List.append_nil] at hevs
  subst hevs
  exact ⟨core, hcore, rfl⟩

theorem input_bind_unmodeled_inv {A : Type} (k : SyscallInput → Sys A) (i : SyscallInput)
    (m : Model) (h : bind input k i m Unmodeled) : k i i m Unmodeled := by
  rcases h with hin | ⟨i', m1, evs1, hin, hk⟩
  · exact absurd hin (by simp only [input, reduceCtorEq, not_false_eq_true])
  · simp only [input, outcome.Ok.injEq] at hin
    obtain ⟨rfl, rfl, rfl⟩ := hin
    exact hk

/-- The same two, for the `get_model` a spec reads right after its input;
what opens that way is on Rocq's `Prelude.get_model_bind_ok_inv`. -/
theorem get_model_bind_ok_inv {A : Type} (k : Model → Sys A) (i : SyscallInput) (m : Model)
    (x : A) (m' : Model) (evs : List event) (h : bind get_model k i m (Ok x m' evs)) :
    k m i m (Ok x m' evs) :=
  (bind_get_model_iff k i m (Ok x m' evs)).mp h

theorem get_model_bind_unmodeled_inv {A : Type} (k : Model → Sys A) (i : SyscallInput)
    (m : Model) (h : bind get_model k i m Unmodeled) : k m i m Unmodeled :=
  (bind_get_model_iff k i m Unmodeled).mp h

theorem record_copyins_unmodeled_inv (reads : List (word × Nat)) (spec : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (h : record_copyins reads spec i m Unmodeled) :
    spec i m Unmodeled := by
  rcases h with hcore | ⟨core, m1, evs1, hcore, hpure⟩
  · exact hcore
  · exact absurd hpure (by simp only [Monad.pure, reduceCtorEq, not_false_eq_true])

/-- Peel an `i <- input ;; m <- get_model ;; ...` prologue, over every
outcome, keeping the body's hypothesis under a name a later step can
still pass on; which arms open this way is on Rocq's
`Prelude.bind_input_model_inv`. -/
theorem bind_input_model_inv {A : Type} (k : SyscallInput → Model → Sys A) (i : SyscallInput)
    (m : Model) (o : outcome A)
    (h : bind input (fun i0 => bind get_model (fun m0 => k i0 m0)) i m o) : k i m i m o := by
  cases o with
  | Ok y m2 evs =>
    exact get_model_bind_ok_inv (fun m0 => k i m0) i m y m2 evs
      (input_bind_ok_inv (fun i0 => bind get_model (fun m0 => k i0 m0)) i m y m2 evs h)
  | Unmodeled =>
    exact get_model_bind_unmodeled_inv (fun m0 => k i m0) i m
      (input_bind_unmodeled_inv (fun i0 => bind get_model (fun m0 => k i0 m0)) i m h)

/-- The one-reader case of the same peel, for an arm that opens with
`m <- get_model ;; ...` alone. -/
theorem bind_model_inv {A : Type} (k : Model → Sys A) (i : SyscallInput) (m : Model)
    (o : outcome A) (h : bind get_model k i m o) : k m i m o :=
  (bind_get_model_iff k i m o).mp h

/-- `Uaccess.access_ok_zero` as an acceptor: when the kernel moved no
bytes, the range verdict is all that is left, so either the arm's own
zero answer stands, or the only admissible return is -EFAULT, or the
model declines. -/
def eff_is_errno (code : Int) (eff : SyscallEffect) : Bool :=
  match eff with
  | SyscallEffect.mkEffectU r [] [] [] [] [] => bv_eqb r (errno_ret code)
  | _ => false

/-! ## The tactics

Rocq's `srw`, `hrw`, `hall`, `bool_true`, `inv_ok` and `sys_unfold`, as
macros.  Rocq's `cbv beta iota zeta` is Lean's `dsimp only` (beta, iota,
zeta, projections, no lemmas), wrapped in `try` because `dsimp only`
fails where `cbv` merely does nothing. -/

/-- `srw E`: rewrite with `E`, then re-reduce.  `srw E at h` is Rocq's
`hrw E in H`. -/
macro "srw " e:term loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (rw [$e:term] $[$loc]?; try dsimp only $[$loc]?))

/-- Rocq's `hrw E in H`, under its own name. -/
macro "hrw " e:term " at " h:ident : tactic =>
  `(tactic| (rw [$e:term] at $h:ident; try dsimp only at $h:ident))

/-- Rewrite an equation wherever it applies and re-reduce everything —
used when `inv_ok` has already renamed the interesting hypothesis. -/
macro "hall " e:term : tactic =>
  `(tactic| ((try rw [$e:term] at *); try dsimp only at *))

/-- Rocq's `bool_true`, arm for arm.  The first arm is the same rewrite;
the three hypothesis-driven arms — `H : x = y` under a `bv_eqb x y` or a
`Z.eqb x y`, and `H : b = true` under a `b` — are one `simp only [*]`
pass closed off by the reflexive facts they leave behind, since Lean
cannot match a hypothesis against the goal from inside a macro.  That
pass is WIDER than Rocq's three arms: it rewrites with every hypothesis
that is an equation, of any shape, so an `h : a = b + 1` in context
rewrites `a` away where Rocq's would not have touched it, and it uses a
hypothesis `h : P` or `h : ¬ P` as `P = True` or `P = False`.  The two
`destruct (a <=? b)` / `destruct (a <? b)` arms, which keep the branch
`lia` cannot refute, are one `split` whose `isFalse` goal `omega` must
close; it takes any `if` `omega` can settle that way, on `Int` or on
`Nat`, and where `split` finds an `if` whose false branch `omega`
cannot refute the arm fails and the loop stops, where Rocq would have
gone on to the next comparison: a proof that meets that case splits it
by hand. -/
macro "bool_true" : tactic =>
  `(tactic| repeat first
    | rw [bv_eqb_refl]
    | (simp only [*, bv_eqb_refl, decide_true, Bool.true_and, Bool.and_true, ↓reduceIte])
    | (split
       case isFalse _ => omega))

/-! `inv_ok` takes hypotheses apart, and Lean's tactic language cannot
name a hypothesis by its shape from inside a macro: `rcases ‹∃ _, _›`
elaborates the anonymous term to a copy and leaves the original in
place, so a `repeat` over it never ends.  The two steps below are the
elaborated form of Rocq's arms; `inv_ok` itself is the `repeat` over
them. -/

open Lean Meta Elab Tactic in
/-- Rocq's `progress subst`: `subst_vars`, failing when it substituted
nothing (`substVars` hands back the same goal in that case). -/
elab "inv_ok_subst" : tactic =>
  liftMetaTactic1 fun g => do
    let g' ← substVars g
    if g' == g then throwError "inv_ok: nothing to substitute"
    return some g'

open Lean Meta Elab Tactic in
/-- Rocq's hypothesis arms: the first hypothesis, in context order, that
is an `exists` or an `and` is taken apart by `cases`, which clears it;
the first that is an equation between two constructor applications is
taken apart by `injection`, which clears it and leaves one equation per
component (Rocq's `inversion H; clear H` on `Ok`, `Some` and `CheckOk`;
`inv_ok_subst` then substitutes the components that are variables) or,
on `Ok _ _ _ = Unmodeled` or `Some _ = None`, closes the goal (Rocq's
four `discriminate` arms); an `or` is taken only when nothing of the
other shapes is left, as Rocq's `first` orders it.  Any constructor
pair is treated the same way, which Rocq's list did not need to say. -/
elab "inv_ok_hyp" : tactic => do
  let g ← getMainGoal
  let shape (d : LocalDecl) (orArm : Bool) : MetaM (Option FVarId) := do
    if d.isImplementationDetail then return none
    let t := (← instantiateMVars d.type).consumeMData
    if orArm then
      return if t.isAppOfArity ``Or 2 then some d.fvarId else none
    if t.isAppOfArity ``Exists 2 || t.isAppOfArity ``And 2 then return some d.fvarId
    if t.isAppOfArity ``Eq 3 then
      let lhs := (t.getArg! 1).consumeMData
      let rhs := (t.getArg! 2).consumeMData
      if (← isConstructorApp lhs) && (← isConstructorApp rhs) then return some d.fvarId
    return none
  let fv? ← g.withContext do
    match ← (← getLCtx).findDeclM? (shape · false) with
    | some fv => pure (some fv)
    | none => (← getLCtx).findDeclM? (shape · true)
  let some fv := fv? | throwError "inv_ok: no hypothesis to take apart"
  let isEq ← g.withContext do
    return ((← instantiateMVars (← fv.getType)).consumeMData).isAppOfArity ``Eq 3
  if isEq then
    match ← Lean.Meta.injection g fv with
    | .solved => replaceMainGoal []
    | .subgoal g' _ _ => replaceMainGoal [g']
  else
    let subgoals ← g.cases fv
    replaceMainGoal (subgoals.map (·.mvarId)).toList

/-- Decompose monadic hypotheses (after the combinators are unfolded).
Arm for arm with Rocq's: `progress subst` is `inv_ok_subst`; `cbv beta
zeta in *` is `dsimp only at *`, which fails on its own when it does
nothing — and which also reduces a `match` on a constructor and a
projection of a constructor, where Rocq's arm asked for no `iota`, so the
two can leave a hypothesis in different shapes (a `match` Rocq's would
have kept is reduced here); a difference in what is left standing, never
in what is provable; the `exists` / `and` / `or` destructs and the `Ok = Ok`,
`Some = Some`, `CheckOk = CheckOk` inversions are `inv_ok_hyp`; and
`H : False` is `contradiction`, which also closes a goal on a
constructor mismatch `inv_ok_hyp` has not reached yet. -/
macro "inv_ok" : tactic =>
  `(tactic| repeat first
    | inv_ok_subst
    | dsimp only at *
    | contradiction
    | inv_ok_hyp)

/-- Unfold the DSL down to its primitives everywhere: sugar first,
primitive combinators last, so everything bottoms out.  Rocq's list
minus the one name the Lean tree lacks, as the file's preamble records.
`simp only … at *` rather than `unfold … at *`, because Lean's `unfold`
fails on a name that does not occur while Rocq's does nothing; the
difference is that this also beta-reduces and reduces a `match` on a
constructor, which is what the `cbv` every Rocq caller runs next does.
With `-failIfUnchanged`, because `simp only … at *` fails when nothing
anywhere changes and Rocq's `unfold … in *` succeeds there.  Not `try`:
a quoted name is resolved at the use site, so under `try` a misspelled
or since-renamed name in this list would make the macro silently do
nothing, while `-failIfUnchanged` still reports an unknown constant. -/
macro "sys_unfold" : tactic =>
  `(tactic| simp -failIfUnchanged only [Sys.Syscall.record_copyins, State.with_copyins,
      Sys.Syscall.err_ret, Sys.Syscall.ret_only, Sys.Syscall.errno_from, Sys.Fs.File.lowest_fd,
      Monad.set_fds, Monad.set_pipes, Monad.set_vmmaps, Monad.add_vm_lazy, Monad.forget_vm_range,
      Monad.set_stdin, Monad.set_urandom, Monad.set_fs, Monad.set_halted, Monad.set_tid,
      Monad.set_rlimit_core, Monad.set_utsname, Monad.set_statpin, Monad.set_setsid_succeeded,
      Monad.set_clock, Monad.set_creds, Monad.set_sigmask, Monad.set_sigaltstack_installed,
      Sys.Kernel.Signal.set_sigmask_deliver, Monad.set_sigabrt_pending, Monad.set_killed,
      Monad.get_model, Monad.get_fds, Monad.get_vmmaps, Monad.modify, Monad.input, Monad.sysno,
      Monad.arg,
      Monad.bind, Monad.pure, Monad.choose, Monad.alt, Monad.unmodeled, Monad.emit] at *)

theorem error_b_big (r : word) (h : addr_is_error_b r = true) :
    18446744073709547520 < bv_unsigned r := by
  unfold addr_is_error_b two_pow_64 at h
  rw [decide_eq_true_eq] at h
  omega

/-- `bind_ok` with the event concatenation as an explicit equation. -/
theorem bind_ok_eq {A B : Type} (c : Sys A) (k : A → Sys B) (i : SyscallInput) (m : Model)
    (x : A) (m1 : Model) (evs1 : List event) (y : B) (m2 : Model) (evs2 evs : List event)
    (hc : c i m (Ok x m1 evs1)) (hk : k x i m1 (Ok y m2 evs2)) (hevs : evs = evs1 ++ evs2) :
    bind c k i m (Ok y m2 evs) := by
  subst hevs
  exact bind_ok c k i m x m1 evs1 y m2 evs2 hc hk

/-- `bind_ok` specialised to a first component that emits no events —
every reader/state accessor in the DSL.  Why plain `bind_ok` cannot be
applied against a CONCRETE event list is on Rocq's `Prelude.bind_ok0`. -/
theorem bind_ok0 {A B : Type} (c : Sys A) (k : A → Sys B) (i : SyscallInput) (m : Model)
    (x : A) (m1 : Model) (y : B) (m2 : Model) (evs : List event)
    (hc : c i m (Ok x m1 [])) (hk : k x i m1 (Ok y m2 evs)) : bind c k i m (Ok y m2 evs) :=
  bind_ok_eq c k i m x m1 [] y m2 evs evs hc hk (List.nil_append evs).symm

theorem check_ret_only_ok_iff (eff : SyscallEffect) (r : word) (m1 : Model) (evs1 : List event)
    (m' : Model) (evs : List event) :
    check_ret_only eff r m1 evs1 = CheckOk m' evs ↔
    (eff = mkEffect r [] [] ∧ m' = m1 ∧ evs = evs1) := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons w ws =>
    simp only [check_ret_only, reduceCtorEq, mkEffect, SyscallEffect.mkEffectU.injEq, false_and,
      and_false]
  | nil =>
  cases zs with
  | cons z zs =>
    simp only [check_ret_only, reduceCtorEq, mkEffect, SyscallEffect.mkEffectU.injEq, false_and,
      and_false]
  | nil =>
  cases us with
  | cons u us =>
    simp only [check_ret_only, reduceCtorEq, mkEffect, SyscallEffect.mkEffectU.injEq, false_and,
      and_false]
  | nil =>
  cases cs with
  | cons c cs =>
    simp only [check_ret_only, reduceCtorEq, mkEffect, SyscallEffect.mkEffectU.injEq, false_and,
      and_false]
  | nil =>
  cases copyins with
  | cons c copyins =>
    simp only [check_ret_only, reduceCtorEq, mkEffect, SyscallEffect.mkEffectU.injEq, false_and,
      and_false]
  | nil =>
  simp only [check_ret_only, mkEffect, SyscallEffect.mkEffectU.injEq, and_true]
  cases hE : bv_eqb ret r with
  | true =>
    rw [bv_eqb_eq] at hE
    subst hE
    simp only [↓reduceIte, check_result.CheckOk.injEq, true_and]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩,
      fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff, not_and]
    intro hret
    subst hret
    rw [bv_eqb_refl] at hE
    exact absurd hE (by simp only [reduceCtorEq, not_false_eq_true])

theorem check_ret_only_copyins_ok_iff (reads : List (word × Nat)) (eff : SyscallEffect)
    (r : word) (m1 : Model) (evs1 : List event) (m' : Model) (evs : List event) :
    check_ret_only_copyins reads eff r m1 evs1 = CheckOk m' evs ↔
    (eff = with_copyins reads (mkEffect r [] []) ∧ m' = m1 ∧ evs = evs1) := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  simp only [check_ret_only_copyins, clear_copyins, with_copyins]
  cases hcore : check_ret_only (SyscallEffect.mkEffectU ret ws zs us cs []) r m1 evs1 with
  | CheckOk m'' evs' =>
    rw [check_ret_only_ok_iff] at hcore
    obtain ⟨heff, rfl, rfl⟩ := hcore
    simp only [mkEffect, SyscallEffect.mkEffectU.injEq] at heff
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := heff
    cases hr : access_ranges_eqb copyins reads with
    | true =>
      rw [access_ranges_eqb_eq] at hr
      subst hr
      simp only [↓reduceIte, check_result.CheckOk.injEq, true_and]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩,
      fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff, not_and,
        SyscallEffect.mkEffectU.injEq, true_and]
      intro hc
      subst hc
      rw [access_ranges_eqb_refl] at hr
      exact absurd hr (by simp only [reduceCtorEq, not_false_eq_true])
  | CheckReject =>
    simp only [reduceCtorEq, false_iff, not_and, SyscallEffect.mkEffectU.injEq]
    intro heff
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heff
    have hok := (check_ret_only_ok_iff (SyscallEffect.mkEffectU ret [] [] [] [] []) ret m1 evs1
      m1 evs1).mpr ⟨rfl, rfl, rfl⟩
    rw [hok] at hcore
    exact absurd hcore (by simp only [reduceCtorEq, not_false_eq_true])
  | CheckUnmodeled =>
    simp only [reduceCtorEq, false_iff, not_and, SyscallEffect.mkEffectU.injEq]
    intro heff
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heff
    simp only [check_ret_only, bv_eqb_refl, ↓reduceIte, reduceCtorEq] at hcore

theorem check_ret_only_no_unmodeled (eff : SyscallEffect) (r : word) (m1 : Model)
    (evs1 : List event) : check_ret_only eff r m1 evs1 ≠ CheckUnmodeled := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons w ws => simp only [check_ret_only, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases zs with
  | cons z zs => simp only [check_ret_only, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases us with
  | cons u us => simp only [check_ret_only, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases cs with
  | cons c cs => simp only [check_ret_only, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases copyins with
  | cons c copyins => simp only [check_ret_only, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  simp only [check_ret_only]
  cases bv_eqb ret r <;> simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem check_ret_only_copyins_no_unmodeled (reads : List (word × Nat)) (eff : SyscallEffect)
    (r : word) (m1 : Model) (evs1 : List event) :
    check_ret_only_copyins reads eff r m1 evs1 ≠ CheckUnmodeled := by
  unfold check_ret_only_copyins
  cases hcore : check_ret_only (clear_copyins eff) r m1 evs1 with
  | CheckOk m'' evs' =>
    cases access_ranges_eqb eff.eff_copyins reads <;>
      simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]
  | CheckReject => simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  | CheckUnmodeled => exact absurd hcore (check_ret_only_no_unmodeled _ r m1 evs1)

theorem check_ret_only_copyins_refl (reads : List (word × Nat)) (r : word) (m : Model)
    (evs : List event) :
    check_ret_only_copyins reads (with_copyins reads (mkEffect r [] [])) r m evs = CheckOk m evs :=
  (check_ret_only_copyins_ok_iff reads _ r m evs m evs).mpr ⟨rfl, rfl, rfl⟩

/-! ## Bridges for the channel short-write acceptors

The claimed return decodes to the delivered prefix's length. -/

theorem len_word_unsigned {A : Type} (l : List A) (hl : (l.length : Int) < two_pow_64) :
    bv_unsigned (len_word l) = (l.length : Int) := by
  unfold two_pow_64 at hl
  unfold len_word Z_to_bv bv_unsigned
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  omega

theorem firstn_length_le_Z {A : Type} (l : List A) (r : Int) (h0 : 0 ≤ r)
    (hle : r ≤ (l.length : Int)) : ((l.take r.toNat).length : Int) = r := by
  rw [List.length_take]
  omega

/-- The delivered prefix's `len_word` is the return value that selected
it — the step every short-write site would otherwise re-derive. -/
theorem len_word_firstn_ret (ret : word) {A : Type} (l : List A)
    (h : 0 ≤ bv_unsigned ret ∧ bv_unsigned ret ≤ (l.length : Int)) :
    len_word (l.take (bv_unsigned ret).toNat) = ret := by
  unfold len_word
  rw [firstn_length_le_Z l (bv_unsigned ret) h.1 h.2]
  unfold Z_to_bv bv_unsigned
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## read -/

theorem neq_einval_of_not_error (r : word) (h : addr_is_error_b r = false) :
    bv_eqb (errno_ret EINVAL) r = false := by
  cases hE : bv_eqb (errno_ret EINVAL) r with
  | false => rfl
  | true =>
    rw [bv_eqb_eq] at hE
    subst hE
    rw [errno_ret_error_b EINVAL (by decide) (by decide)] at h
    exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

theorem eff_is_errno_true (code : Int) (eff : SyscallEffect) (h : eff_is_errno code eff = true) :
    eff = mkEffect (errno_ret code) [] [] := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons w ws => simp only [eff_is_errno, Bool.false_eq_true] at h
  | nil =>
  cases zs with
  | cons z zs => simp only [eff_is_errno, Bool.false_eq_true] at h
  | nil =>
  cases us with
  | cons u us => simp only [eff_is_errno, Bool.false_eq_true] at h
  | nil =>
  cases cs with
  | cons c cs => simp only [eff_is_errno, Bool.false_eq_true] at h
  | nil =>
  cases copyins with
  | cons c copyins => simp only [eff_is_errno, Bool.false_eq_true] at h
  | nil =>
  simp only [eff_is_errno, bv_eqb_eq] at h
  subst h
  rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
