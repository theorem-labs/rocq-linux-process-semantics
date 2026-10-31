-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/State.v
import LinuxProcessSemantics.LinuxProcessSem.BvBase
import LinuxProcessSemantics.LinuxProcessSem.State.Geometry

/-! rocq-baseline: 7b4cf49586658ecbffbab14145ab0969272a0b23 -/

/-! # LinuxProcessSem.State.Readers — reading user memory

One part of `State.v`'s twin, re-exported by `State.lean`, whose header
says how the ten parts divide the Rocq file, what a part may hold and
where the pins live.

WHAT GOES HERE: the byte and string readers of `State.v` — the
chunked `read_bytes_map` walk and the shape proofs use, the
copy_from_user short-copy prefix `readable_bytes`, the pathname
readers, `read_u64`, riscv64 `access_okb` and the copy that follows
it — and the iovec family (ticket A4): the two limits, the descriptor
decoders, the import path, the aggregate clamp and the scatter/gather
walks, in the section at the end of the file.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.State

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! ## Reading user memory (buffers and NUL-terminated strings) — ticket A3

The byte and string readers of `State.v`, ported name for name.  Each
definition keeps its Rocq twin's name; the arguments — why `read_bytes_map`
EXECUTES as a chunked accumulator loop while `read_bytes_aux` is the shape
proofs use, why `readable_bytes` is the copy_from_user short-copy prefix,
why `access_okb` is scoped to the MMU half — are on the Rocq definitions
(`State.read_bytes_aux`, `State.read_bytes_map`, `State.readable_bytes`,
`State.access_okb`, `State.copy_bytes_map`) and are not repeated here.
Two library spellings differ from Rocq's: `List.reverseAux` is Rocq's
`rev_append`, and `Int.toNat` is `Z.to_nat`. -/

/-- The shape proofs use.  Why the checker may not EXECUTE it on a long
range, and why the address advances with wrapping `bv` addition, are on
`State.read_bytes_aux`. -/
def read_bytes_aux (mp : word → Option byte) (a : word) (k : Nat)
    : Option (List byte) :=
  match k with
  | 0 => some []
  | k' + 1 =>
    match mp a with
    | none => none
    | some b =>
      match read_bytes_aux mp (a + 1) k' with
      | some r => some (b :: r)
      | none => none

/-- The chunk the accumulator loops hand their fuel out in
(`State.wmem_chunk`, where the extraction-depth argument lives). -/
def wmem_chunk : Int := 4096

def read_bytes_acc (mp : word → Option byte) (a : word) (k : Nat)
    (acc : List byte) : Option (List byte) :=
  match k with
  | 0 => some acc
  | k' + 1 =>
    match mp a with
    | none => none
    | some b => read_bytes_acc mp (a + 1) k' (b :: acc)

def read_bytes_chunks (mp : word → Option byte) (a : word)
    (q k : Nat) (acc : List byte) : Option (List byte) :=
  match q with
  | 0 => some acc
  | q' + 1 =>
    match read_bytes_acc mp a k acc with
    | none => none
    | some acc' => read_bytes_chunks mp (a + nat_to_word k) q' k acc'

/-- `read_bytes_aux` over `len` bytes, executed as `State.read_bytes_map`
executes it.  `read_bytes_map_eq` is the equation every proof goes
through; nothing outside this block unfolds the body. -/
def read_bytes_map (mp : word → Option byte) (a len : word)
    : Option (List byte) :=
  let n := bv_unsigned len
  match read_bytes_chunks mp a (n / wmem_chunk).toNat wmem_chunk.toNat [] with
  | none => none
  | some acc =>
    match read_bytes_acc mp (a + Z_to_bv 64 (n / wmem_chunk * wmem_chunk))
            (n % wmem_chunk).toNat acc with
    | none => none
    | some acc' => some (List.reverseAux acc' [])

/-! The two bitvector facts the split lemmas step through: `nat_to_word`
is `BitVec.ofNat`, and stepping the address once and then by `j` is
stepping it by `j + 1`. -/

theorem nat_to_word_eq_ofNat (n : Nat) : nat_to_word n = BitVec.ofNat 64 n :=
  BitVec.ofInt_natCast 64 n

theorem nat_to_word_zero : nat_to_word 0 = 0#64 := by decide

theorem add_one_nat_to_word (a : word) (j : Nat) :
    a + 1 + nat_to_word j = a + nat_to_word (j + 1) := by
  rw [nat_to_word_eq_ofNat, nat_to_word_eq_ofNat, BitVec.ofNat_add,
    BitVec.add_assoc, BitVec.add_comm 1]
  rfl

theorem read_bytes_acc_aux (mp : word → Option byte) (k : Nat) (a : word)
    (acc : List byte) :
    read_bytes_acc mp a k acc
      = match read_bytes_aux mp a k with
        | none => none
        | some w => some (List.reverseAux w acc) := by
  induction k generalizing a acc with
  | zero => rfl
  | succ k ih =>
    simp only [read_bytes_acc, read_bytes_aux]
    cases h : mp a with
    | none => rfl
    | some b =>
      dsimp only
      rw [ih]
      cases read_bytes_aux mp (a + 1) k with
      | none => rfl
      | some w => rfl

theorem read_bytes_aux_split (mp : word → Option byte) (j k : Nat) (a : word) :
    read_bytes_aux mp a (j + k)
      = match read_bytes_aux mp a j with
        | none => none
        | some w1 =>
          match read_bytes_aux mp (a + nat_to_word j) k with
          | none => none
          | some w2 => some (w1 ++ w2) := by
  induction j generalizing a with
  | zero =>
    simp only [Nat.zero_add, read_bytes_aux, nat_to_word_zero, BitVec.add_zero]
    cases read_bytes_aux mp a k with
    | none => rfl
    | some w2 => rfl
  | succ j ih =>
    rw [Nat.succ_add]
    simp only [read_bytes_aux]
    cases h : mp a with
    | none => rfl
    | some b =>
      dsimp only
      rw [ih, add_one_nat_to_word]
      cases read_bytes_aux mp (a + 1) j with
      | none => rfl
      | some w1 =>
        cases read_bytes_aux mp (a + nat_to_word (j + 1)) k with
        | none => rfl
        | some w2 => rfl

theorem read_bytes_chunks_flat (mp : word → Option byte) (q k : Nat) (a : word)
    (acc : List byte) :
    read_bytes_chunks mp a q k acc
      = match read_bytes_aux mp a (q * k) with
        | none => none
        | some w => some (List.reverseAux w acc) := by
  induction q generalizing a acc with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ q ih =>
    simp only [read_bytes_chunks, read_bytes_acc_aux, Nat.succ_mul]
    rw [Nat.add_comm (q * k) k, read_bytes_aux_split]
    cases read_bytes_aux mp a k with
    | none => rfl
    | some w1 =>
      dsimp only
      rw [ih]
      cases read_bytes_aux mp (a + nat_to_word k) (q * k) with
      | none => rfl
      | some w2 =>
        simp only [List.reverseAux_eq, List.reverse_append, List.append_assoc]

/-- The decomposition `read_bytes_map_eq` rests on: `len` split into its
chunk count and remainder, in `Nat`. -/
theorem word_to_nat_chunks (len : word) :
    (bv_unsigned len / wmem_chunk).toNat * wmem_chunk.toNat
      + (bv_unsigned len % wmem_chunk).toNat = word_to_nat len := by
  unfold wmem_chunk word_to_nat bv_unsigned
  have h4 : (4096 : Int).toNat = 4096 := rfl
  rw [h4]
  omega

/-- ...and the chunked address is the `nat_to_word` of that product. -/
theorem chunk_addr_eq (a len : word) :
    a + Z_to_bv 64 (bv_unsigned len / wmem_chunk * wmem_chunk)
      = a + nat_to_word ((bv_unsigned len / wmem_chunk).toNat * wmem_chunk.toNat) := by
  have h4 : (4096 : Int).toNat = 4096 := rfl
  have hn : 0 ≤ bv_unsigned len := by unfold bv_unsigned; omega
  have hz : 0 ≤ bv_unsigned len / wmem_chunk * wmem_chunk := by
    unfold wmem_chunk; omega
  have hnat : (bv_unsigned len / wmem_chunk * wmem_chunk).toNat
      = (bv_unsigned len / wmem_chunk).toNat * wmem_chunk.toNat := by
    unfold wmem_chunk; rw [h4]; omega
  rw [nat_to_word_eq_ofNat, ← hnat]
  unfold Z_to_bv
  rw [← Int.toNat_of_nonneg hz, BitVec.ofInt_natCast, Int.toNat_natCast]

theorem read_bytes_map_eq (mp : word → Option byte) (a len : word) :
    read_bytes_map mp a len = read_bytes_aux mp a (word_to_nat len) := by
  simp only [read_bytes_map]
  rw [read_bytes_chunks_flat, chunk_addr_eq, ← word_to_nat_chunks, read_bytes_aux_split]
  cases read_bytes_aux mp a
      ((bv_unsigned len / wmem_chunk).toNat * wmem_chunk.toNat) with
  | none => rfl
  | some w1 =>
    dsimp only
    rw [read_bytes_acc_aux]
    cases read_bytes_aux mp
        (a + nat_to_word ((bv_unsigned len / wmem_chunk).toNat * wmem_chunk.toNat))
        (bv_unsigned len % wmem_chunk).toNat with
    | none => rfl
    | some w2 =>
      simp only [List.reverseAux_eq, List.reverse_append, List.reverse_reverse,
        List.append_nil]

/-- What `copy_from_user` moves before faulting: the raw copy's uncopied
count comes back and the copied prefix stands (include/linux/uaccess.h,
`_inline_copy_from_user`, v6.18.46).  The execution-shape argument is on
`State.readable_bytes_aux`. -/
def readable_bytes_aux (mp : word → Option byte) (a : word) (k : Nat)
    : List byte :=
  match k with
  | 0 => []
  | k' + 1 =>
    match mp a with
    | none => []
    | some b => b :: readable_bytes_aux mp (a + 1) k'

theorem readable_bytes_aux_length_le (mp : word → Option byte) (k : Nat) (a : word) :
    (readable_bytes_aux mp a k).length ≤ k := by
  induction k generalizing a with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [readable_bytes_aux]
    cases mp a with
    | none => simp only [List.length_nil]; omega
    | some b =>
      simp only [List.length_cons]
      have := ih (a + 1)
      omega

/-- The one thing this walk carries that `read_bytes_acc` does not, and
why, is on `State.readable_bytes_acc`. -/
def readable_bytes_acc (mp : word → Option byte) (a : word) (k : Nat)
    (acc : List byte) : Bool × List byte :=
  match k with
  | 0 => (true, acc)
  | k' + 1 =>
    match mp a with
    | none => (false, acc)
    | some b => readable_bytes_acc mp (a + 1) k' (b :: acc)

def readable_bytes_chunks (mp : word → Option byte) (a : word)
    (q k : Nat) (acc : List byte) : Bool × List byte :=
  match q with
  | 0 => (true, acc)
  | q' + 1 =>
    match readable_bytes_acc mp a k acc with
    | (false, acc') => (false, acc')
    | (true, acc') => readable_bytes_chunks mp (a + nat_to_word k) q' k acc'

/-- `readable_bytes_aux` over `len` bytes, executed as `State.readable_bytes`
executes it; `readable_bytes_eq` is the equation every proof goes through. -/
def readable_bytes (mp : word → Option byte) (a len : word) : List byte :=
  let n := bv_unsigned len
  match readable_bytes_chunks mp a (n / wmem_chunk).toNat wmem_chunk.toNat [] with
  | (false, acc) => List.reverseAux acc []
  | (true, acc) =>
    List.reverseAux
      (readable_bytes_acc mp (a + Z_to_bv 64 (n / wmem_chunk * wmem_chunk))
        (n % wmem_chunk).toNat acc).2 []

theorem readable_bytes_acc_flat (mp : word → Option byte) (k : Nat) (a : word)
    (acc : List byte) :
    readable_bytes_acc mp a k acc
      = (decide ((readable_bytes_aux mp a k).length = k),
         List.reverseAux (readable_bytes_aux mp a k) acc) := by
  induction k generalizing a acc with
  | zero => rfl
  | succ k ih =>
    cases h : mp a with
    | none =>
      have h0 : ¬ (([] : List byte).length = k + 1) := by
        simp only [List.length_nil]; omega
      simp only [readable_bytes_acc, readable_bytes_aux, h, decide_eq_false h0,
        List.reverseAux_nil]
    | some b =>
      simp only [readable_bytes_acc, readable_bytes_aux, h]
      rw [ih]
      simp only [List.length_cons, Nat.add_right_cancel_iff, List.reverseAux_cons]

/-- Splitting the walk at `j`: the second part is reached exactly when the
first ran to its full length (`State.readable_bytes_aux_split`). -/
theorem readable_bytes_aux_split (mp : word → Option byte) (j k : Nat) (a : word) :
    readable_bytes_aux mp a (j + k)
      = if (readable_bytes_aux mp a j).length = j
        then readable_bytes_aux mp a j ++ readable_bytes_aux mp (a + nat_to_word j) k
        else readable_bytes_aux mp a j := by
  induction j generalizing a with
  | zero =>
    simp only [Nat.zero_add, readable_bytes_aux, List.length_nil, nat_to_word_zero,
      BitVec.add_zero, List.nil_append, ite_true]
  | succ j ih =>
    rw [Nat.succ_add]
    cases hm : mp a with
    | none =>
      have h : ¬ (([] : List byte).length = j + 1) := by
        simp only [List.length_nil]; omega
      simp only [readable_bytes_aux, hm, h, ↓reduceIte]
    | some b =>
      simp only [readable_bytes_aux, hm]
      rw [ih, add_one_nat_to_word]
      by_cases h : (readable_bytes_aux mp (a + 1) j).length = j
      · simp only [h, List.length_cons, ↓reduceIte, List.cons_append]
      · simp only [h, List.length_cons, Nat.add_right_cancel_iff, ↓reduceIte]

theorem readable_bytes_chunks_flat (mp : word → Option byte) (q k : Nat) (a : word)
    (acc : List byte) :
    readable_bytes_chunks mp a q k acc
      = (decide ((readable_bytes_aux mp a (q * k)).length = q * k),
         List.reverseAux (readable_bytes_aux mp a (q * k)) acc) := by
  induction q generalizing a acc with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ q ih =>
    simp only [readable_bytes_chunks, readable_bytes_acc_flat, Nat.succ_mul]
    rw [Nat.add_comm (q * k) k, readable_bytes_aux_split]
    have hle := readable_bytes_aux_length_le mp k a
    by_cases hk : (readable_bytes_aux mp a k).length = k
    · simp only [hk, decide_true, ↓reduceIte]
      rw [ih]
      simp only [List.length_append, hk, Nat.add_left_cancel_iff, List.reverseAux_eq,
        List.reverse_append, List.append_assoc]
    · simp only [hk, decide_false, ↓reduceIte]
      have hne : ¬ ((readable_bytes_aux mp a k).length = k + q * k) := by omega
      rw [decide_eq_false hne]

theorem readable_bytes_eq (mp : word → Option byte) (a len : word) :
    readable_bytes mp a len = readable_bytes_aux mp a (word_to_nat len) := by
  simp only [readable_bytes]
  rw [readable_bytes_chunks_flat, chunk_addr_eq, ← word_to_nat_chunks,
    readable_bytes_aux_split]
  by_cases hfull : (readable_bytes_aux mp a
      ((bv_unsigned len / wmem_chunk).toNat * wmem_chunk.toNat)).length
      = (bv_unsigned len / wmem_chunk).toNat * wmem_chunk.toNat
  · simp only [hfull, decide_true, ↓reduceIte, readable_bytes_acc_flat,
      List.reverseAux_eq, List.reverse_append, List.reverse_reverse, List.append_nil]
  · simp only [hfull, decide_false, ↓reduceIte, List.reverseAux_eq,
      List.reverse_reverse, List.append_nil]

/-- The readable prefix never exceeds the requested count. -/
theorem readable_bytes_length_le (mp : word → Option byte) (a len : word) :
    ((readable_bytes mp a len).length : Int) ≤ bv_unsigned len := by
  rw [readable_bytes_eq]
  have := readable_bytes_aux_length_le mp (word_to_nat len) a
  unfold word_to_nat at this ⊢
  unfold bv_unsigned
  omega

/-- Linux `PATH_MAX` (include/uapi/linux/limits.h, v6.18.46), counting the
NUL: `getname_flags` answers `-ENAMETOOLONG` exactly when
`strncpy_from_user` returns `PATH_MAX` (fs/namei.c, `getname_flags`,
v6.18.46). -/
def path_max : Nat := 4096

/-- Pathname bytes counted as read: through the first NUL, the first
unreadable byte, or the fuel.  No longer than what `getname()` issues, and
usually shorter, since `strncpy_from_user` loads whole words except on
an unaligned source (lib/strncpy_from_user.c, `do_strncpy_from_user`,
v6.18.46); the cost is argued on
`State.cstr_access_len_aux` and in
`linux-process-semantics@ff0313ba4f:bugs/openat-getname-word-at-a-time.md`. -/
def cstr_access_len_aux (mp : word → Option byte) (a : word) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    match mp a with
    | none => 1
    | some b =>
      if bv_eqb b (Z_to_bv 8 0) then 1
      else cstr_access_len_aux mp (a + 1) fuel' + 1

/-- The three outcomes of reading a pathname, which Linux keeps apart:
`getname_flags` returns `strncpy_from_user`'s `-EFAULT` as it is and
turns a `PATH_MAX`-long copy into `-ENAMETOOLONG` (fs/namei.c,
`getname_flags`, v6.18.46).  Both failures are kernel returns, not
modeling gaps (`State.cstr_result`). -/
inductive cstr_result : Type
  | CstrOk (p : List byte)   -- NUL-terminated within PATH_MAX
  | CstrTooLong              -- no NUL within PATH_MAX        -> -ENAMETOOLONG
  | CstrFault                -- unmapped byte before the NUL  -> -EFAULT
  deriving DecidableEq, Repr

export cstr_result (CstrOk CstrTooLong CstrFault)

def read_cstr_aux (mp : word → Option byte) (a : word) (k : Nat) : cstr_result :=
  match k with
  | 0 => CstrTooLong             -- no NUL within the length bound
  | k' + 1 =>
    match mp a with
    | none => CstrFault          -- unmapped byte before the NUL
    | some b =>
      if bv_eqb b (Z_to_bv 8 0) then CstrOk []
      else
        match read_cstr_aux mp (a + 1) k' with
        | CstrOk r => CstrOk (b :: r)
        | r => r                 -- propagate the failure verbatim

def read_cstr (mp : word → Option byte) (a : word) : cstr_result :=
  read_cstr_aux mp a path_max

/-- One 64-bit field of an in-memory kernel structure, in the hart's byte
order: riscv is little-endian (arch/riscv/include/uapi/asm/byteorder.h
includes linux/byteorder/little_endian.h, v6.18.46), and
`BvBase.le_bytes_to_word` decodes index 0 as least significant. -/
def read_u64 (mp : word → Option byte) (a : word) : Option word :=
  match read_bytes_map mp a (Z_to_bv 64 8) with
  | some bs => some (le_bytes_to_word bs)
  | none => none

/-- riscv64 `access_ok`, transcribed: `__access_ok` is
`(size <= TASK_SIZE_MAX) && (addr <= TASK_SIZE_MAX - size)`
(include/asm-generic/access_ok.h, `__access_ok`, v6.18.46 / 1f99e9ab748f),
with `TASK_SIZE_MAX` the header's own fallback to `TASK_SIZE`, which is
what riscv64 gets at that commit: neither arch/riscv/include/asm/pgtable.h
nor arch/riscv/include/asm/uaccess.h defines one.  Written as
a SUBTRACTION, as the kernel writes it, so a range wrapping 2^64 is refused.
The pointer-masking and `CONFIG_MMU` halves of the argument, and the
scoping to the MMU configuration, are on `State.access_okb`. -/
def access_okb (base : word) (len : Int) : Bool :=
  (len ≤ TASK_SIZE) && (bv_unsigned base ≤ TASK_SIZE - len)

/-- `copy_to_user`/`copy_from_user` IS `access_ok` AND THEN THE COPY
(include/linux/uaccess.h, `_inline_copy_from_user` and
`_inline_copy_to_user`, v6.18.46, each test `access_ok` over the whole
range and only then call the raw copy).  On the copy-in side that test
sits behind `!can_do_masked_user_access()`, which is 0 on riscv because
arch/riscv/include/asm/uaccess.h defines no `masked_user_access_begin`
(include/linux/uaccess.h, the `#ifdef masked_user_access_begin` fallback,
v6.18.46).  `read_bytes_map` is the copy
alone and wraps; `access_okb` sums in `Int` and refuses the wrapped range.
THE LENGTH IS AN `Int` because `access_okb`'s is (`State.copy_bytes_map`). -/
def copy_bytes_map (mp : word → Option byte) (a : word) (len : Int)
    : Option (List byte) :=
  if access_okb a len then read_bytes_map mp a (Z_to_bv 64 len) else none

/-- A range `access_okb` refuses is `none` however the memory map answers. -/
theorem copy_bytes_map_refused (mp : word → Option byte) (a : word) (len : Int) :
    access_okb a len = false → copy_bytes_map mp a len = none := by
  intro h
  simp only [copy_bytes_map, h, Bool.false_eq_true, ↓reduceIte]

/-- ...and on a range `access_okb` accepts, exactly the walk it always was. -/
theorem copy_bytes_map_accepted (mp : word → Option byte) (a : word) (len : Int) :
    access_okb a len = true →
    copy_bytes_map mp a len = read_bytes_map mp a (Z_to_bv 64 len) := by
  intro h
  simp only [copy_bytes_map, h, ↓reduceIte]

/-! `le32_bytes` is in `State/Pipes.lean` (the pipe helpers landed it
first); its pins stay with the readers in `Checks/Cases/State.lean`. -/


/-! ## The iovec family — ticket A4

The vectored-transfer helpers of `State.v`, the `read_iovecs_aux` …
`writev_gathered` block: the two Linux limits, the descriptor decoders,
the import path with its errno order, the aggregate clamp, and the
scatter/gather over a destination or source vector.  The section sits
ahead of the A12 section because that is Rocq's order: the block follows
the A3 readers in `State.v` and precedes everything A12 mirrors.  The
arguments that are not kernel facts — why `read_iovecs_aux` has no caller
in the model and exists for
the OCaml conformance tester, why `read_iovecs` bounds the fuel at
`IOV_MAX` and loses nothing by it, why `MAX_RW_COUNT` is scoped to 4 KiB
page hosts (
`linux-process-semantics@ff0313ba4f:bugs/max-rw-count-hardcoded-page-size.md`) — are on the Rocq
definitions (`State.read_iovecs_aux`, `State.read_iovecs`,
`State.MAX_RW_COUNT`, `State.import_iovecs`) and are not repeated here.
Every kernel claim below was read at Linux v6.18.46 (commit
1f99e9ab748f).

Library spellings that differ from Rocq's: `Z.min` is `min` on `Int`,
`firstn`/`skipn` are `List.take`/`List.drop`, `forallb` is `List.all`,
`concat (map snd …)` is `(….map Prod.snd).flatten`, and `Z.to_nat` is
`Int.toNat`.  The Rocq proofs step through stdpp's `Z_to_bv_unsigned`
and `bv_wrap_small`; `BvBase.bv_unsigned_Z_to_bv_small` is that pair as
one lemma. -/

/-- `cnt` `struct iovec` entries from `a`: on LP64 each is 16 bytes,
`iov_base` then `iov_len`, both 8-byte words (include/uapi/linux/uio.h,
`struct iovec`, v6.18.46) — or `none` if any byte of the array is unmapped.
The layout decode alone, with no length or address validation: no arm of
the model calls it, and why the OCaml conformance tester does is on
`State.read_iovecs_aux`. -/
def read_iovecs_aux (mp : word → Option byte) (a : word) (k : Nat)
    : Option (List (word × word)) :=
  match k with
  | 0 => some []
  | k' + 1 =>
    match read_u64 mp a, read_u64 mp (a + 8) with
    | some base, some len =>
      match read_iovecs_aux mp (a + 16) k' with
      | some r => some ((base, len) :: r)
      | none => none
    | _, _ => none

/-- Linux caps every transfer at `MAX_RW_COUNT = INT_MAX & PAGE_MASK`
(include/linux/fs.h, `MAX_RW_COUNT`, v6.18.46).  `PAGE_MASK` is a host
property, so this is the 4 KiB-page value; that scope, and why it is not
made configurable, are on `State.MAX_RW_COUNT` and in
`linux-process-semantics@ff0313ba4f:bugs/max-rw-count-hardcoded-page-size.md`. -/
def MAX_RW_COUNT : Int := 0x7ffff000

/-- The scalar clamp: `if (count > MAX_RW_COUNT) count = MAX_RW_COUNT;`
in `vfs_read` and `vfs_write` (fs/read_write.c, v6.18.46), after
`access_ok` and `rw_verify_area` and ahead of the `->read`/`->write`
dispatch, so an over-clamp count is a SHORT transfer, not an error.
Which arms consume it is on `State.rw_count_clamp`. -/
def rw_count_clamp (count : word) : Int :=
  min (bv_unsigned count) MAX_RW_COUNT

theorem rw_count_clamp_small (count : word) (h : bv_unsigned count ≤ MAX_RW_COUNT) :
    rw_count_clamp count = bv_unsigned count := by
  unfold rw_count_clamp
  omega

theorem rw_count_clamp_range (count : word) :
    0 ≤ rw_count_clamp count ∧ rw_count_clamp count ≤ MAX_RW_COUNT := by
  unfold rw_count_clamp MAX_RW_COUNT bv_unsigned
  omega

/-- The clamped count re-entered as a `word`: `MAX_RW_COUNT` is far under
2^64, so the round trip is the identity. -/
theorem rw_count_clamp_word (count : word) :
    bv_unsigned (Z_to_bv 64 (rw_count_clamp count)) = rw_count_clamp count := by
  have h := rw_count_clamp_range count
  apply bv_unsigned_Z_to_bv_small
  · exact h.1
  · unfold MAX_RW_COUNT at h; omega

/-- Linux `UIO_MAXIOV`, the largest iovec count one `readv`/`writev`
may pass: `iovec_from_user` answers `-EINVAL` above it (lib/iov_iter.c,
`iovec_from_user`, testing `nr_segs > UIO_MAXIOV`; the constant is
`UIO_MAXIOV = 1024` in include/uapi/linux/uio.h; both v6.18.46). -/
def IOV_MAX : Int := 1024

/-- The iovec array a `readv`/`writev` of count `cnt` passes, decoded with
at most `IOV_MAX` entries of fuel.  Why the bound is faithful rather than
an approximation — the `nr_segs > UIO_MAXIOV` test in `iovec_from_user`
(lib/iov_iter.c, v6.18.46) fires before any descriptor is copied, and the
one path around it imports a single entry — is on `State.read_iovecs`;
`read_iovecs_unguarded` proves the bound invisible at and below it. -/
def read_iovecs (mp : word → Option byte) (a cnt : word)
    : Option (List (word × word)) :=
  read_iovecs_aux mp a (word_to_nat_bounded cnt IOV_MAX.toNat)

theorem read_iovecs_unguarded (mp : word → Option byte) (a cnt : word)
    (hle : bv_unsigned cnt ≤ IOV_MAX) :
    read_iovecs mp a cnt = read_iovecs_aux mp a (word_to_nat cnt) := by
  unfold read_iovecs
  have hb : word_to_nat_bounded cnt IOV_MAX.toNat = word_to_nat cnt := by
    unfold word_to_nat_bounded
    have hc : bv_unsigned cnt ≤ (IOV_MAX.toNat : Int) := by
      unfold IOV_MAX at hle ⊢
      omega
    simp only [hc, ↓reduceIte]
  rw [hb]

/-- The three outcomes of importing an iovec array (lib/iov_iter.c,
`__import_iovec`, v6.18.46): the imported entries, a `-EFAULT` from an
unreadable descriptor or a failed `access_ok`, or a `-EINVAL` from a
count over `IOV_MAX` or a length negative as `ssize_t`. -/
inductive iov_import : Type
  | ImpOk (iovs : List (word × word))
  | ImpFault
  | ImpInval
  deriving DecidableEq, Repr

export iov_import (ImpOk ImpFault ImpInval)

/-- One `struct iovec` as `copy_iovec_from_user` fetches it (lib/iov_iter.c,
v6.18.46): BOTH fields are loaded — `iov_len`, then `iov_base`, each an
`unsafe_get_user` with its own fixup — and only then is `len < 0` tested.
So a field that cannot be read is `-EFAULT` whatever the length says, and
a negative length is `-EINVAL` only once both fields have been read
(`State.iov_entry` records the revision that got this wrong). -/
inductive iov_entry : Type
  | IovEntry (base len : word)
  | IovFault
  | IovInval
  deriving DecidableEq, Repr

export iov_entry (IovEntry IovFault IovInval)

def read_iovec_entry (mp : word → Option byte) (a : word) : iov_entry :=
  match read_u64 mp a, read_u64 mp (a + 8) with
  | some base, some len =>
    if (2 : Int) ^ 63 ≤ bv_unsigned len then IovInval else IovEntry base len
  | _, _ => IovFault

/-- `copy_iovec_from_user` (lib/iov_iter.c, v6.18.46): ONE interleaved
pass in index order — per entry both fields, then `if (len < 0) return
-EINVAL` — so the FIRST error in INDEX ORDER decides the call.  That
this is v6.4 and later, and which commit made it so, is on
`State.copy_iovecs_aux`. -/
def copy_iovecs_aux (mp : word → Option byte) (a : word) (k : Nat) : iov_import :=
  match k with
  | 0 => ImpOk []
  | k' + 1 =>
    match read_iovec_entry mp a with
    | IovFault => ImpFault
    | IovInval => ImpInval
    | IovEntry base len =>
      match copy_iovecs_aux mp (a + 16) k' with
      | ImpOk r => ImpOk ((base, len) :: r)
      | r => r

/-- The descriptors `copy_iovecs_aux` actually attempted, one 16-byte
range per descriptor reached; the walk stops on the same first unreadable
descriptor or negative length, so an errno path records only the prefix
the kernel inspected.  The range is the whole descriptor whichever of the
kernel's two 8-byte loads (`iov_len`, then `iov_base`) faulted: the
ledger is kept at descriptor granularity, a superset of the bytes
touched. -/
def copy_iovecs_accesses (mp : word → Option byte) (a : word) (k : Nat)
    : List (word × Nat) :=
  match k with
  | 0 => []
  | k' + 1 =>
    (a, 16) ::
      match read_iovec_entry mp a with
      | IovEntry _ _ => copy_iovecs_accesses mp (a + 16) k'
      | _ => []

/-- `__import_iovec`'s per-segment `access_ok(iov_base, len)` on the
UNCAPPED length (lib/iov_iter.c, `__import_iovec`, v6.18.46), applied to
a zero-length entry as to any other. -/
def iovs_access_okb (iovs : List (word × word)) : Bool :=
  iovs.all (fun bl => access_okb bl.1 (bv_unsigned bl.2))

/-- Truncate an iovec sequence at `MAX_RW_COUNT`, as `__import_iovec`'s
loop does with `len > MAX_RW_COUNT - total_len` (lib/iov_iter.c,
`__import_iovec`, v6.18.46).  Entries after the cap remain present with
length zero: the kernel imports and address-checks the whole array
before I/O, though no byte of those entries can be transferred. -/
def cap_iovecs_aux (iovs : List (word × word)) (left : Int) : List (word × word) :=
  match iovs with
  | [] => []
  | (base, len) :: rest =>
    let n := min left (bv_unsigned len)
    (base, Z_to_bv 64 n) :: cap_iovecs_aux rest (left - n)

def cap_iovecs (iovs : List (word × word)) : List (word × word) :=
  cap_iovecs_aux iovs MAX_RW_COUNT

/-- The iovec import path, `import_iovec` → `__import_iovec` (lib/iov_iter.c,
v6.18.46), for readv and writev alike.  The entries come back UNCAPPED;
the consumers clamp afterwards.  Three shapes, in the kernel's order:

- a count of exactly ONE is `__import_iovec`'s first statement and takes
  `__import_iovec_ubuf`: one descriptor through `copy_iovec_from_user`
  (the `read_iovec_entry` order), then `import_ubuf`, which caps to
  `MAX_RW_COUNT` FIRST and applies `access_ok` to the CAPPED length —
  ahead of `iovec_from_user`, hence of its `UIO_MAXIOV` test;
- a count of zero is `iovec_from_user`'s early return: nothing is copied
  and the array address is never tested;
- every other count is `iovec_from_user` (the `UIO_MAXIOV` test, then —
  for counts above `UIO_FASTIOV` = 8 — a `kmalloc_array` whose failure is
  a `-ENOMEM` outside the model,
  `linux-process-semantics@ff0313ba4f:bugs/writev-heap-iovec-enomem-not-admitted.md`, then
  `copy_iovec_from_user` with `user_access_begin` over the whole array,
  then the index-ordered `-EFAULT`/`-EINVAL` walk) followed by
  `__import_iovec`'s SECOND pass, `access_ok` on each UNCAPPED length.
  The two passes are why a `-EINVAL` at ANY index beats an `access_ok`
  `-EFAULT` at any index, while an unreadable descriptor and a negative
  length race in index order.

Why `n = 1` never reports `-EINVAL` for a count over `IOV_MAX`, and what a
raw count of `2^32 + 1` does on the way in, are on `State.import_iovecs`. -/
def import_iovecs (mp : word → Option byte) (a n : word) : iov_import :=
  if bv_eqb n (Z_to_bv 64 1) then
    if !access_okb a 16 then ImpFault
    else
      match read_iovec_entry mp a with
      | IovFault => ImpFault
      | IovInval => ImpInval
      | IovEntry base len =>
        if !access_okb base (min (bv_unsigned len) MAX_RW_COUNT) then ImpFault
        else ImpOk [(base, len)]
  else if bv_eqb n (Z_to_bv 64 0) then ImpOk []
  else if IOV_MAX < bv_unsigned n then ImpInval
  else if !access_okb a (16 * bv_unsigned n) then ImpFault
  else
    match copy_iovecs_aux mp a (word_to_nat n) with
    | ImpOk iovs => if iovs_access_okb iovs then ImpOk iovs else ImpFault
    | r => r

/-- The descriptor ranges `import_iovecs` read, branch for branch. -/
def import_iovecs_accesses (mp : word → Option byte) (a n : word) : List (word × Nat) :=
  if bv_eqb n (Z_to_bv 64 1) then
    if !access_okb a 16 then [] else [(a, 16)]
  else if bv_eqb n (Z_to_bv 64 0) then []
  else if IOV_MAX < bv_unsigned n then []
  else if !access_okb a (16 * bv_unsigned n) then []
  else copy_iovecs_accesses mp a (word_to_nat n)

/-- The copy-in ledger for the prefix of an iovec sequence a transfer of
`left` bytes touched.  `word_to_nat_bounded` rather than `Nat.min`, as Rocq
spells it: the reason on `State.iov_prefix_accesses` is the unary numeral
Rocq's extraction would build for a capped `iov_len`, a cost Lean's `Nat`
does not have; the spelling is kept so the two definitions stay
identical. -/
def iov_prefix_accesses (iovs : List (word × word)) (left : Nat) : List (word × Nat) :=
  match iovs, left with
  | _, 0 => []
  | [], _ => []
  | (base, len) :: rest, _ =>
    let n := word_to_nat_bounded len left
    if n = 0 then iov_prefix_accesses rest left
    else (base, n) :: iov_prefix_accesses rest (left - n)

/-- Scatter `bs` across destination iovecs in order, as `iterate_iovec`
walks the segments of a vector of two or more entries (include/linux/iov_iter.h,
`iterate_iovec`, v6.18.46; one descriptor is an `ITER_UBUF`, whose
`iterate_ubuf` takes the single step with the same result — same file,
`iterate_ubuf`, `iterate_and_advance2`): a zero-length segment is skipped
without its base being touched (`if (likely(part))`), and every nonempty
piece must be writable in `mp`.  `none` means `bs` exceeds the aggregate capacity or some byte
that would be delivered is not writable. -/
def scatter_iovecs (mp : word → Option byte) (iovs : List (word × word))
    (bs : List byte) : Option (List (word × List byte)) :=
  match bs with
  | [] => some []
  | _ :: _ =>
    match iovs with
    | [] => none
    | (base, len) :: rest =>
      let n := word_to_nat_bounded len bs.length
      let here := bs.take n
      let later := bs.drop n
      match here with
      | [] => scatter_iovecs mp rest later
      | _ :: _ =>
        match read_bytes_map mp base (len_word here), scatter_iovecs mp rest later with
        | some _, some writes => some ((base, here) :: writes)
        | _, _ => none

/-- What a successful scatter writes, concatenated in order, is exactly
the delivered string. -/
theorem scatter_iovecs_concat (mp : word → Option byte) (iovs : List (word × word)) :
    ∀ (bs : List byte) (writes : List (word × List byte)),
      scatter_iovecs mp iovs bs = some writes → (writes.map Prod.snd).flatten = bs := by
  induction iovs with
  | nil =>
    intro bs writes h
    cases bs with
    | nil =>
      simp only [scatter_iovecs, Option.some.injEq] at h
      subst h
      rfl
    | cons b bs' =>
      simp only [scatter_iovecs] at h
      cases h
  | cons p rest ih =>
    obtain ⟨base, len⟩ := p
    intro bs writes h
    cases bs with
    | nil =>
      simp only [scatter_iovecs, Option.some.injEq] at h
      subst h
      rfl
    | cons b bs' =>
      have hsplit := List.take_append_drop (word_to_nat_bounded len (b :: bs').length) (b :: bs')
      cases hhere : (b :: bs').take (word_to_nat_bounded len (b :: bs').length) with
      | nil =>
        -- a zero-length segment is skipped: the delivery is unchanged
        rw [hhere, List.nil_append] at hsplit
        simp only [scatter_iovecs, hhere] at h
        rw [ih _ _ h, hsplit]
      | cons x xs =>
        rw [hhere] at hsplit
        cases hr : read_bytes_map mp base (len_word (x :: xs)) with
        | none =>
          simp only [scatter_iovecs, hhere, hr] at h
          cases h
        | some ok =>
          cases ht : scatter_iovecs mp rest
              ((b :: bs').drop (word_to_nat_bounded len (b :: bs').length)) with
          | none =>
            simp only [scatter_iovecs, hhere, hr, ht] at h
            cases h
          | some tail =>
            simp only [scatter_iovecs, hhere, hr, ht, Option.some.injEq] at h
            subst h
            simp only [List.map_cons, List.flatten_cons]
            rw [ih _ _ ht]
            exact hsplit

/-- An empty delivery performs no writes, independently of the vector. -/
theorem scatter_iovecs_nil (mp : word → Option byte) (iovs : List (word × word)) :
    scatter_iovecs mp iovs [] = some [] := by
  cases iovs <;> rfl

/-- Whether a one-byte scatter succeeds depends only on the destination
vector and its writability, not on the value of the byte. -/
theorem scatter_iovecs_singleton_some (mp : word → Option byte) (iovs : List (word × word)) :
    ∀ (b : byte) (writes : List (word × List byte)) (b' : byte),
      scatter_iovecs mp iovs [b] = some writes →
      ∃ writes', scatter_iovecs mp iovs [b'] = some writes' := by
  induction iovs with
  | nil =>
    intro b writes b' h
    simp only [scatter_iovecs] at h
    cases h
  | cons p rest ih =>
    obtain ⟨base, len⟩ := p
    intro b writes b' h
    have hlen : ([b] : List byte).length = 1 := rfl
    have hlen' : ([b'] : List byte).length = 1 := rfl
    simp only [scatter_iovecs, hlen] at h
    simp only [scatter_iovecs, hlen']
    -- a one-byte delivery takes either nothing or the whole byte from a segment
    have hcases : word_to_nat_bounded len 1 = 0 ∨ word_to_nat_bounded len 1 = 1 := by
      unfold word_to_nat_bounded
      split
      · rename_i hc
        unfold bv_unsigned at hc
        unfold word_to_nat
        omega
      · exact Or.inr rfl
    rcases hcases with h0 | h1
    · rw [h0] at h ⊢
      simp only [List.take_zero, List.drop_zero] at h ⊢
      exact ih b writes b' h
    · rw [h1] at h ⊢
      have ht1 : ([b] : List byte).take 1 = [b] := rfl
      have hd1 : ([b] : List byte).drop 1 = [] := rfl
      have ht1' : ([b'] : List byte).take 1 = [b'] := rfl
      have hd1' : ([b'] : List byte).drop 1 = [] := rfl
      have hlw : len_word [b'] = len_word [b] := rfl
      simp only [ht1, hd1, scatter_iovecs_nil] at h
      simp only [ht1', hd1', scatter_iovecs_nil, hlw]
      cases hr : read_bytes_map mp base (len_word [b]) with
      | none =>
        simp only [hr] at h
        cases h
      | some ok => exact ⟨[(base, [b'])], rfl⟩

/-- The source bytes of each iovec in order, flattened (`none` if any
source byte is unreadable) — exactly the buffer an equivalent single
`write` would write. -/
def gather_iovecs (mp : word → Option byte) (iovs : List (word × word))
    : Option (List byte) :=
  match iovs with
  | [] => some []
  | (base, len) :: r =>
    match read_bytes_map mp base len with
    | none => none
    | some bs =>
      match gather_iovecs mp r with
      | some rest => some (bs ++ rest)
      | none => none

/-- The GATHERABLE PREFIX of an iovec sequence: the bytes a writev moves
before faulting.  `iterate_iovec` consumes the segments in order and
stops at the first short step (include/linux/iov_iter.h, `iterate_iovec`,
the `skip < p->iov_len` break, v6.18.46; a single descriptor is an
`ITER_UBUF` and `iterate_ubuf` takes its one step, same file), the step being
`copy_from_user_iter` (lib/iov_iter.c, v6.18.46) calling `raw_copy_from_user`
(arch/riscv/include/asm/uaccess.h, v6.18.46), so a fault inside an iovec delivers that iovec's readable prefix and
stops — the flattened analogue of `readable_bytes`.  Equals the full
flattening exactly when every source byte is readable; a zero-length
iovec is skipped without its base being touched.  The completeness test
compares lengths in `Int` over the unsigned value. -/
def gather_prefix (mp : word → Option byte) (iovs : List (word × word)) : List byte :=
  match iovs with
  | [] => []
  | (base, len) :: r =>
    let bs := readable_bytes mp base len
    if (bs.length : Int) = bv_unsigned len then bs ++ gather_prefix mp r else bs

/-- Total byte count an iovec list requests — writev's `-EFAULT` gate: a
delivery of zero bytes is an error only when something was requested,
because `vfs_writev` returns 0 outright when the aggregate is 0
(fs/read_write.c, `vfs_writev`, v6.18.46) while `generic_perform_write`
answers `-EFAULT` only when nothing of a nonzero request was written
(mm/filemap.c, `generic_perform_write`, v6.18.46).  Summed in `Int` over
unsigned lengths, so the total cannot wrap. -/
def iovs_total (iovs : List (word × word)) : Int :=
  match iovs with
  | [] => 0
  | (_, len) :: r => bv_unsigned len + iovs_total r

theorem iovs_total_nonneg (iovs : List (word × word)) : 0 ≤ iovs_total iovs := by
  induction iovs with
  | nil => simp only [iovs_total]; omega
  | cons p rest ih =>
    obtain ⟨base, len⟩ := p
    simp only [iovs_total]
    unfold bv_unsigned
    omega

/-- `cap_iovecs` IS the kernel's aggregate clamp, stated here in general
(the pins state instances): capping a vector leaves an aggregate of
exactly `min` of the original aggregate and `MAX_RW_COUNT`.  The
generalized form quantifies over the budget `left` still unspent, which
is what the induction needs; `iovs_total_cap` instantiates it. -/
theorem iovs_total_cap_aux (iovs : List (word × word)) :
    ∀ left : Int, 0 ≤ left →
      iovs_total (cap_iovecs_aux iovs left) = min (iovs_total iovs) left := by
  induction iovs with
  | nil =>
    intro left hleft
    simp only [cap_iovecs_aux, iovs_total]
    omega
  | cons p rest ih =>
    obtain ⟨base, len⟩ := p
    intro left hleft
    simp only [cap_iovecs_aux, iovs_total]
    have hlen := len.isLt
    have hrest := iovs_total_nonneg rest
    have hn : 0 ≤ min left (bv_unsigned len) := by unfold bv_unsigned; omega
    rw [bv_unsigned_Z_to_bv_small _ hn (by unfold bv_unsigned; omega)]
    rw [ih (left - min left (bv_unsigned len)) (by omega)]
    unfold bv_unsigned at *
    omega

theorem iovs_total_cap (iovs : List (word × word)) :
    iovs_total (cap_iovecs iovs) = min (iovs_total iovs) MAX_RW_COUNT := by
  unfold cap_iovecs
  apply iovs_total_cap_aux
  unfold MAX_RW_COUNT
  omega

/-- The bytes a writev moves, and the `-EFAULT` gate in front of them,
each stated ONCE: `__import_iovec` applies the aggregate `MAX_RW_COUNT`
clamp inside its per-segment loop for BOTH directions (lib/iov_iter.c,
`__import_iovec`, v6.18.46), so the write side gathers over `cap_iovecs`
exactly as the read side scatters over it. -/
def writev_gathered (mp : word → Option byte) (iovs0 : List (word × word)) : List byte :=
  gather_prefix mp (cap_iovecs iovs0)


end LinuxProcessSemantics.LinuxProcessSem.State
