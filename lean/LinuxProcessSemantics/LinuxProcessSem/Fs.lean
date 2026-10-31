-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Fs.v
import LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # LinuxProcessSem.Fs — the interpreted file-system model

Mirrors `theories/LinuxProcessSem/Fs.v` at rocq-linux-process-semantics
`f1006fe8`: every definition of that file under its Rocq name, every
lemma of it, plus the helper lemmas those twins' proofs need and nothing
else.  The
pins, and the `fs_remove` lookup laws that are no twin of a Rocq lemma,
are `Checks/Cases/Fs.lean`.  `bv_eqb_eq`
is the one twin declared `protected`: `Riscv/Prelude.lean` already proves it
in the form every file here uses, and a file opening both namespaces
should keep a single `bv_eqb_eq` in scope.

TRUST BOUNDARY: this file is part of the trusted specification.

Paths and file contents are `byte = BitVec 8` lists; offsets and counts
arrive from registers as `word = BitVec 64` and are bridged to `Nat` for
the list operations.  The file system is an INTERNAL, INTERPRETED model: a
finite map from paths to byte contents, threaded through the syscall
model, whose initial image is an input to the program and which is
OBSERVED ONLY AT EXIT.

CANONICAL FORM: because the final map appears inside a trace event
compared with `=`, the representation must not depend on the order in
which files were written.  The association list is kept strictly sorted
by path (`fs_sorted`); `fs_set` and `fs_remove` preserve sortedness, so two
runs that create the same files with the same contents produce equal `Fs`
values.  `valid_fs` requires the initial image to be sorted as well.  The
argument in full is the header of `theories/LinuxProcessSem/Fs.v`.

Rocq's `firstn`, `skipn` and `repeat x n` are `List.take`, `List.drop`
and `List.replicate n x` (the count moves first); Rocq's `Z` comparisons
on offsets are Lean's decidable `≤` on `Int`; `Forall` over the image is a
bounded `∀`.  Nothing else in the definitions is spelled differently. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Fs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-- A path is the raw byte string the program passed to the kernel (no
NUL terminator).  Paths are uninterpreted: there is no directory
structure, no normalization ("./x" and "x" are different files), and no
symlinks.  That is a statement about this MAP, not about what the model
accepts: a spec that would have to walk a path to answer correctly is
expected to decline rather than read the map as if it had walked one;
grep for `path_has_slash` to see the current set.  The consequence
worth keeping, argued at `path` in `theories/LinuxProcessSem/Fs.v`: the
only spec that CREATES a key is `Open.create_wronly`, and it sits behind
that guard, so no program can make "./x" and "x" two keys. -/
abbrev path : Type := List byte

def path_eqb (p q : path) : Bool :=
  match p, q with
  | [], [] => true
  | a :: p', b :: q' => bv_eqb a b && path_eqb p' q'
  | _, _ => false

/-- Twin of Rocq's `bv_eqb_eq`, which `Fs.v` states itself.  Lean already
has it as `Riscv.Prelude.bv_eqb_eq`, where
`bv_eqb` is `BitVec`'s decidable equality rather than Rocq's `Z.eqb` on
`bv_unsigned`; this twin is `protected` so it never competes with that
name under `open`. -/
protected theorem bv_eqb_eq {n : Nat} (a b : BitVec n) :
    bv_eqb a b = true ↔ a = b :=
  LinuxProcessSemantics.Riscv.Prelude.bv_eqb_eq a b

theorem path_eqb_eq (p q : path) : path_eqb p q = true ↔ p = q := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons b q => constructor <;> intro h <;> cases h
  | cons a p ih =>
    cases q with
    | nil => constructor <;> intro h <;> cases h
    | cons b q =>
      simp only [path_eqb, Bool.and_eq_true, bv_eqb_eq, ih, List.cons.injEq]

theorem path_eqb_refl (p : path) : path_eqb p p = true := (path_eqb_eq p p).2 rfl

/-- Strict lexicographic order on paths (shorter prefixes first); bytes
compare unsigned. -/
def path_ltb (p q : path) : Bool :=
  match p, q with
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: p', b :: q' => bv_ltu a b || (bv_eqb a b && path_ltb p' q')

/-- The file system: a path-to-contents association list, kept strictly
sorted by `path_ltb` (see the canonical-form note above). -/
abbrev Fs : Type := List (path × List byte)

def fs_lookup (fs : Fs) (p : path) : Option (List byte) :=
  match fs with
  | [] => none
  | (q, data) :: r => if path_eqb p q then some data else fs_lookup r p

/-- Insert-or-replace, preserving strict sortedness of the keys. -/
def fs_set (fs : Fs) (p : path) (data : List byte) : Fs :=
  match fs with
  | [] => [(p, data)]
  | (q, d) :: r =>
      if path_ltb p q then (p, data) :: (q, d) :: r
      else if path_eqb p q then (p, data) :: r
      else (q, d) :: fs_set r p data

/-- `bv_ltu` read back in `Nat`: `BitVec.ult` is the decided `<` on
`toNat`. -/
theorem bv_ltu_eq_true {n : Nat} (a b : BitVec n) :
    bv_ltu a b = true ↔ a.toNat < b.toNat := by
  simp only [bv_ltu, BitVec.ult, decide_eq_true_eq]

theorem bv_eqb_eq_toNat {n : Nat} (a b : BitVec n) :
    bv_eqb a b = true ↔ a.toNat = b.toNat := by
  rw [bv_eqb_eq, BitVec.toNat_eq]

/-- `path_ltb` is transitive.  This is what makes "drop one entry"
preserve the canonical form: the neighbours either side of a removed key
were separated only through it. -/
theorem path_ltb_trans (a b c : path) :
    path_ltb a b = true → path_ltb b c = true → path_ltb a c = true := by
  induction a generalizing b c with
  | nil =>
    cases b with
    | nil => intro h; cases h
    | cons y b =>
      cases c with
      | nil => intro _ h; cases h
      | cons z c => intro _ _; rfl
  | cons x a ih =>
    cases b with
    | nil => intro h; cases h
    | cons y b =>
      cases c with
      | nil => intro _ h; cases h
      | cons z c =>
        simp only [path_ltb, Bool.or_eq_true, Bool.and_eq_true, bv_ltu_eq_true,
          bv_eqb_eq_toNat]
        intro h1 h2
        rcases h1 with h1 | ⟨hx1, hp1⟩ <;> rcases h2 with h2 | ⟨hx2, hp2⟩
        · exact Or.inl (Nat.lt_trans h1 h2)
        · exact Or.inl (by omega)
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, ih b c hp1 hp2⟩

/-- Remove a path.  A path absent from the map leaves it unchanged, so a
caller that has already decided the path is present (unlink) and one that
has not both get the same function.  The removal is real because the
final file system is observable at exit, and Linux removes exactly the one
directory entry the last path component names (`do_unlinkat` /
`vfs_unlink`, fs/namei.c, Linux v6.18.46), which `Checks/Cases/Fs.lean`
holds the function to. -/
def fs_remove (fs : Fs) (p : path) : Fs :=
  match fs with
  | [] => []
  | (q, d) :: r => if path_eqb p q then r else (q, d) :: fs_remove r p

/-- Keys strictly increasing — the canonical form. -/
def fs_sorted (fs : Fs) : Bool :=
  match fs with
  | [] => true
  | (p, _) :: r =>
      match r with
      | [] => true
      | (q, _) :: _ => path_ltb p q && fs_sorted r

/-- The head-key clause of `fs_sorted`, named so the lemmas below can talk
about it. -/
def fs_lt_head (a : path) (fs : Fs) : Bool :=
  match fs with
  | [] => true
  | (q, _) :: _ => path_ltb a q

theorem fs_sorted_cons (p : path) (d : List byte) (r : Fs) :
    fs_sorted ((p, d) :: r) = (fs_lt_head p r && fs_sorted r) := by
  cases r with
  | nil => rfl
  | cons qe r' =>
    obtain ⟨q, e⟩ := qe
    rfl

/-- A key below the head of a sorted list is below the head of its tail. -/
theorem fs_lt_head_trans (a q : path) (r : Fs) :
    path_ltb a q = true → fs_lt_head q r = true → fs_lt_head a r = true := by
  cases r with
  | nil => intro _ _; rfl
  | cons qe r' =>
    obtain ⟨q', e⟩ := qe
    intro hh hq
    exact path_ltb_trans a q q' hh hq

theorem fs_remove_lt_head (fs : Fs) (a p : path) :
    fs_sorted fs = true → fs_lt_head a fs = true →
    fs_lt_head a (fs_remove fs p) = true := by
  induction fs with
  | nil => intro _ hh; exact hh
  | cons qd r ih =>
    obtain ⟨q, d⟩ := qd
    intro hs hh
    rw [fs_sorted_cons, Bool.and_eq_true] at hs
    obtain ⟨hq, hr⟩ := hs
    simp only [fs_remove]
    cases hpq : path_eqb p q with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hh
    | true =>
      simp only [↓reduceIte]
      exact fs_lt_head_trans a q r hh hq

/-- Dropping an entry preserves the canonical form, so a modeled unlink
keeps the final `Fs` comparable with `=` (see the CANONICAL FORM note
above). -/
theorem fs_remove_sorted (fs : Fs) (p : path) :
    fs_sorted fs = true → fs_sorted (fs_remove fs p) = true := by
  induction fs with
  | nil => intro _; rfl
  | cons qd r ih =>
    obtain ⟨q, d⟩ := qd
    intro hs
    rw [fs_sorted_cons, Bool.and_eq_true] at hs
    obtain ⟨hq, hr⟩ := hs
    simp only [fs_remove]
    cases hpq : path_eqb p q with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [fs_sorted_cons, Bool.and_eq_true]
      exact ⟨fs_remove_lt_head r q p hr hq, ih hr⟩
    | true =>
      simp only [↓reduceIte]
      exact hr

/-- `path_ltb` is a total order on distinct keys: two keys that compare
neither below nor equal compare above.  This is what `fs_set` needs to
keep the canonical form when it walks past a key.
Rocq: `Fs.path_ltb_total`. -/
theorem path_ltb_total (p q : path) :
    path_ltb p q = false → path_eqb p q = false → path_ltb q p = true := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => intro _ heq; simp [path_eqb] at heq
    | cons b q => intro hlt _; simp [path_ltb] at hlt
  | cons a p ih =>
    cases q with
    | nil => intro _ _; rfl
    | cons b q =>
      intro hlt heq
      simp only [path_ltb, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hlt
      simp only [path_eqb, Bool.and_eq_false_iff] at heq
      obtain ⟨hab, hrest⟩ := hlt
      cases he : bv_eqb a b with
      | true =>
        have hba : bv_eqb b a = true := by
          have hab' := (bv_eqb_eq a b).1 he
          exact (bv_eqb_eq b a).2 hab'.symm
        have hr : path_ltb p q = false := by
          rcases hrest with h | h
          · rw [he] at h; exact absurd h (by decide)
          · exact h
        have hqe : path_eqb p q = false := by
          rcases heq with h | h
          · rw [he] at h; exact absurd h (by decide)
          · exact h
        simp [path_ltb, hba, ih q hr hqe]
      | false =>
        have hne : a ≠ b := fun h => by rw [h] at he; simp [bv_eqb] at he
        have hlt' : ¬ (a.toNat < b.toNat) := by
          simpa [bv_ltu, BitVec.ult] using hab
        have hnat : a.toNat ≠ b.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
        have hba : bv_ltu b a = true := by
          simp only [bv_ltu, BitVec.ult, decide_eq_true_eq]
          omega
        simp [path_ltb, hba]

/-- Inserting a key above `a` keeps `a` below the head.
Rocq: `Fs.fs_set_lt_head`. -/
theorem fs_set_lt_head (fs : Fs) (a p : path) (d : List byte) :
    path_ltb a p = true → fs_lt_head a fs = true →
    fs_lt_head a (fs_set fs p d) = true := by
  induction fs with
  | nil => intro hap _; exact hap
  | cons qe r ih =>
    obtain ⟨q, e⟩ := qe
    intro hap hh
    simp only [fs_set]
    cases hpq : path_ltb p q with
    | true => simpa [fs_lt_head] using hap
    | false =>
      cases hpe : path_eqb p q with
      | true => simpa [fs_lt_head] using hap
      | false => simpa [fs_lt_head] using hh

/-- Insert-or-replace preserves the canonical form, so a modeled create
or write keeps the final `Fs` comparable with `=` (see the CANONICAL FORM
note above).  Rocq: `Fs.fs_set_sorted`. -/
theorem fs_set_sorted (fs : Fs) (p : path) (d : List byte) :
    fs_sorted fs = true → fs_sorted (fs_set fs p d) = true := by
  induction fs with
  | nil => intro _; rfl
  | cons qe r ih =>
    obtain ⟨q, e⟩ := qe
    intro hs
    simp only [fs_set]
    cases hpq : path_ltb p q with
    | true =>
      simp only [↓reduceIte]
      rw [fs_sorted_cons, Bool.and_eq_true]
      exact ⟨by simpa [fs_lt_head] using hpq, hs⟩
    | false =>
      cases hpe : path_eqb p q with
      | true =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hqp : p = q := (path_eqb_eq p q).1 hpe
        subst hqp
        rw [fs_sorted_cons]
        rw [fs_sorted_cons] at hs
        exact hs
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [fs_sorted_cons, Bool.and_eq_true]
        rw [fs_sorted_cons, Bool.and_eq_true] at hs
        obtain ⟨hh, hr⟩ := hs
        exact ⟨fs_set_lt_head r q p d (path_ltb_total p q hpq hpe) hh, ih hr⟩

/-- A fact that holds of every key of an image and of the key being set
holds of every key afterwards.  `State.fs_seed_tmp_keys` is the caller
this is written for.  Rocq: `Fs.fs_set_keys`. -/
theorem fs_set_keys (P : path → Prop) (fs : Fs) (p : path) (d : List byte)
    (hfs : ∀ pf ∈ fs, P pf.1) (hp : P p) : ∀ pf ∈ fs_set fs p d, P pf.1 := by
  induction fs with
  | nil =>
    intro pf hpf
    simp only [fs_set, List.mem_singleton] at hpf
    subst hpf
    exact hp
  | cons qe r ih =>
    obtain ⟨q, e⟩ := qe
    simp only [fs_set]
    cases hpq : path_ltb p q with
    | true =>
      simp only [↓reduceIte]
      intro pf hpf
      rcases List.mem_cons.1 hpf with rfl | hpf'
      · exact hp
      · exact hfs pf hpf'
    | false =>
      cases hpe : path_eqb p q with
      | true =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        intro pf hpf
        rcases List.mem_cons.1 hpf with rfl | hpf'
        · exact hp
        · exact hfs pf (List.mem_cons_of_mem _ hpf')
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        intro pf hpf
        rcases List.mem_cons.1 hpf with rfl | hpf'
        · exact hfs (q, e) (List.mem_cons_self ..)
        · exact ih (fun x hx => hfs x (List.mem_cons_of_mem _ hx)) pf hpf'

/-- A lookup misses when no key IS the path.  The counterpart of
`fs_set_keys` for the read side: a caller holding a fact about every key
of an image gets the `none` from it without unfolding the recursion.
`Run.absolute_divergent_not_seeded` is the caller this is written for.
Rocq: `Fs.fs_lookup_none_of_keys`. -/
theorem fs_lookup_none_of_keys (fs : Fs) (p : path) (h : ∀ qd ∈ fs, qd.1 ≠ p) :
    fs_lookup fs p = none := by
  induction fs with
  | nil => rfl
  | cons qd r ih =>
    obtain ⟨q, d⟩ := qd
    have hq : q ≠ p := h (q, d) (List.mem_cons_self ..)
    simp only [fs_lookup]
    cases hpq : path_eqb p q with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    | true => exact absurd ((path_eqb_eq p q).1 hpq).symm hq

/-- Validity predicate for an initial file-system image: it must be in
the CANONICAL sorted form (trace events compare final file systems with
`=`, so the representation must be unique — see the header note), and
paths must be NUL-free byte strings so a program can actually name them.
(Bounding clauses on bytes are enforced by the `byte` type.) -/
def valid_fs (fs0 : Fs) : Prop :=
  fs_sorted fs0 = true ∧
  ∀ pf ∈ fs0, ¬ (Z_to_bv 8 0) ∈ pf.1

/-- The byte '/', the one byte this file has to interpret.

Paths are uninterpreted here (see the header), and the separator's
MEANING lives in `Sys.Fs.Namei` — `path_has_slash`, `dir_prefixb` and the
trailing-separator tests are all there.  What is needed at this rung is
only the byte itself, for `key_is_relative` below, and that file sits
above this one, so the constant is spelled here too.  The two are pinned
equal where the second is defined
(`Sys.Fs.Namei.slash_byte_is_path_slash_byte`), so moving either is a
compile error rather than a silent divergence.
Rocq: `Fs.path_slash_byte`. -/
def path_slash_byte : byte := Z_to_bv 8 47

/-- A key is CWD-RELATIVE when it does not begin with the separator.

THE EMPTY KEY COUNTS AS RELATIVE.  It begins with nothing, so it begins
with no '/'; and it is a key no program can name anyway
(`Uaccess.read_cstr` of an empty pathname is the -ENOENT every path spec
answers before it looks anything up), so admitting it costs no reachable
behaviour and excluding it would be a clause about a key nothing reads.

This is a statement about the FIRST byte and about nothing else: a key
may still carry separators inside it ("a/b"), and that key is relative.
What "relative" buys is exactly the one thing the device arms need — such
a key is not, and does not live under, an absolute path like "/dev/null".
Rocq: `Fs.key_is_relative`. -/
def key_is_relative (p : path) : Prop :=
  match p with
  | [] => True
  | b :: _ => b ≠ path_slash_byte

/-- Every key of an image is cwd-relative.

THIS IS NOT A CLAUSE OF `valid_fs`, and the reason is the seeding.
`Run.valid_input` reads `valid_fs` on `State.in_fs`, the image AFTER
`State.fs_seed_tmp` has inserted each declared /tmp entry under the
absolute key "/tmp/<name>"; a clause here would therefore make every
input with a non-empty declaration invalid and silently remove those
inputs from every theorem.  So this predicate is carried by
`Run.valid_input` over `State.in_image_fs`, the PRE-SEED image, as a
conjunct of its own — see the note on that definition.

No boolean twin, because `valid_fs` beside it has none: the image
predicates in this file are read by proofs, not computed by the checker.
Rocq: `Fs.fs_keys_relative`. -/
def fs_keys_relative (fs : Fs) : Prop :=
  ∀ pf ∈ fs, key_is_relative pf.1

/-! ## File contents: byte-list read/write at an offset -/

/-- `List.take` is unchanged when its index is capped at the input list's
length (Rocq's `firstn_min_length`). -/
theorem firstn_min_length {A : Type} (n : Nat) (l : List A) :
    List.take (min n l.length) l = List.take n l := by
  rw [← List.take_take, List.take_length]

/-- The file's bytes from `off` onward, counted down IN `Int` against the
list rather than through a `Nat` index.  This exists so that no read
builds `word_to_nat off`: Rocq's extracted checker keeps `nat` unary, so
that numeral costs one stack frame per unit of `off`, and an lseek can
put `off` anywhere below 2^63.  Recursing on the LIST bounds the work by
the file rather than by the offset.  `file_from_skipn` proves it equal to
the `List.drop` it replaces, so nothing downstream has to know it is
here; the extraction argument in full is at `file_from` in
`theories/LinuxProcessSem/Fs.v`. -/
def file_from (data : List byte) (off : Int) : List byte :=
  match data with
  | [] => []
  | _ :: tl => if off ≤ 0 then data else file_from tl (off - 1)

theorem file_from_skipn (data : List byte) (off : Int) (hoff : 0 ≤ off) :
    file_from data off = List.drop off.toNat data := by
  induction data generalizing off with
  | nil => simp only [file_from, List.drop_nil]
  | cons b tl ih =>
    simp only [file_from]
    by_cases hle : off ≤ 0
    · simp only [hle, ↓reduceIte]
      have h0 : off = 0 := by omega
      subst h0
      rfl
    · simp only [hle, ↓reduceIte]
      rw [ih (off - 1) (by omega)]
      have h1 : off.toNat = (off - 1).toNat + 1 := by omega
      rw [h1, List.drop_succ_cons]

/-- Read up to `count` bytes starting at `off`; truncated at end-of-file.
This is where a file read returns fewer bytes than asked, and 0 bytes at
or past the end: `shmem_file_read_iter` (mm/shmem.c, Linux v6.18.46)
copies nothing at or past `i_size`.

NEITHER argument reaches `Nat` unbounded.  `off` does not cross at all:
`file_from` walks the file in `Int`, so a read is not charged for how far
out it seeks.  `count` crosses only after being capped at what is left
of the file, so a vectored read may name the whole `State.MAX_RW_COUNT`
aggregate without building that numeral.  `file_read_unguarded` proves
the pair is extensionally the ordinary `take`/`drop` definition; see
`file_read` in `theories/LinuxProcessSem/Fs.v` for why the bound sits
here rather than at the callers. -/
def file_read (data : List byte) (off count : word) : List byte :=
  let rest := file_from data (bv_unsigned off)
  List.take (word_to_nat_bounded count rest.length) rest

theorem file_read_unguarded (data : List byte) (off count : word) :
    file_read data off count
      = List.take (word_to_nat count) (List.drop (word_to_nat off) data) := by
  simp only [file_read]
  rw [word_to_nat_bounded_eq_min, firstn_min_length,
    file_from_skipn data (bv_unsigned off) (by simp only [bv_unsigned]; omega)]
  simp only [bv_unsigned, word_to_nat, Int.toNat_natCast]

/-- Overwrite `bs` at offset `off`, extending the file if needed.  A write
of a NONEMPTY `bs` past the current end zero-fills the gap: Linux leaves
a hole, and a hole reads back as zeros (`shmem_file_read_iter`,
mm/shmem.c, Linux v6.18.46, copies from `ZERO_PAGE(0)` where no folio
exists).

A zero-length write leaves the file untouched, as on Linux: `write(fd,
buf, 0)` on a regular file transfers nothing and never extends the file,
even when the fd's offset sits past end-of-file (an lseek can put it
there).  The zero-count exit is `generic_write_checks_count`
(fs/read_write.c, Linux v6.18.46): after only the `IS_SWAPFILE` refusal
it runs `if (!*count) return 0;`, before the `IOCB_APPEND` repositioning
and the size limits; `generic_write_checks` (same file, same version)
then returns 0, and `shmem_file_write_iter` (mm/shmem.c, Linux v6.18.46)
returns that 0 under `if (ret <= 0) goto unlock;` without reaching
`generic_perform_write`.  `theories/LinuxProcessSem/Sys/Fs/ReadWrite.v`
cites the same check under mm/filemap.c; at v6.18.46 the function is in
fs/read_write.c.  Without the `[]` arm the padding below would
zero-extend the file out to `off` on a write that Linux makes no change
for. -/
def file_write (data : List byte) (off : word) (bs : List byte) : List byte :=
  match bs with
  | [] => data
  | _ :: _ =>
      let padded := data ++ List.replicate (word_to_nat off - data.length) (Z_to_bv 8 0)
      List.take (word_to_nat off) padded
        ++ bs ++ List.drop (word_to_nat off + bs.length) padded

/-- Set the file's length to exactly `len`: a SHRINK drops the tail, a
GROW zero-fills out to the new length (`ftruncate`; see
`Open.ftruncate_spec`).

Linux makes the grown region a HOLE rather than allocating it, but a hole
reads back as zero bytes, so a byte list of zeros is the right content:
it is the representation that differs, not the observation.  Read at
Linux v6.18.46 on tmpfs, where the harness's files live: a grow writes
only the size — `shmem_setattr` (mm/shmem.c) does `i_size_write` and
touches the page cache only under `if (newsize <= oldsize)`;
`truncate_setsize` (mm/truncate.c) is not on tmpfs's path.  The grown
region reads as zeros because an index with no folio is copied from
`ZERO_PAGE(0)` by `shmem_file_read_iter` (mm/shmem.c, v6.18.46) and the bytes past
the old EOF in the last cached folio were zeroed at first fill
(`shmem_write_end`, mm/shmem.c, v6.18.46, through include/linux/highmem.h's
`folio_zero_segments`), or cleared whole when a non-write path created
it (`shmem_get_folio_gfp`, mm/shmem.c:2621-2625, `clear_highpage` under
`sgp != SGP_WRITE`), or by the shrink that cut it (mm/shmem.c's
`shmem_undo_range` calling `truncate_inode_partial_folio`, mm/truncate.c,
v6.18.46) — and nothing wrote them since.  The one writer of bytes past
EOF that moves no size is a store through a writable MAP_SHARED mapping
of that folio (`shmem_fault` fills with `SGP_CACHE`, mm/shmem.c:2776),
which the model never has: `Sys/Mm/Mmap.v` declines every file-backed
and every MAP_SHARED request.  `theories/LinuxProcessSem/Fs.v` cites
`truncate_setsize`'s chain for this at v6.1 through v6.12; that chain
zeroes at and past the NEW size, and on a generic filesystem the bytes
between the old and new EOF are whatever its own fill path zeroed —
`pagecache_isize_extended` (mm/truncate.c) only prepares the folio
straddling the old size for a later mmap write — a `comments:` defect
there, not a different observation.

`word_to_nat len` is built in full here and NOTHING IN THIS DEFINITION
BOUNDS IT.  What bounds it is the guard all of its call sites apply
first (`Open.modeled_truncate_gap`: a grow only while
`len ≤ length data + rw_bytes_max`, a shrink with `len ≤ length data`
outright), and the `word_to_nat_bounded` trick `file_read` uses does not
apply, because the `replicate` count is exactly what a grow must add.
The argument in full is at `file_truncate` in
`theories/LinuxProcessSem/Fs.v`. -/
def file_truncate (data : List byte) (len : word) : List byte :=
  List.take (word_to_nat len) data
    ++ List.replicate (word_to_nat len - data.length) (Z_to_bv 8 0)

end LinuxProcessSemantics.LinuxProcessSem.Fs
