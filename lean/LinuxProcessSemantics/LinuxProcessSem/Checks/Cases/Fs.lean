import LinuxProcessSemantics.LinuxProcessSem.Fs

/-! # Checks.Cases.Fs — the file-system model, read off against Linux

Pins over `LinuxProcessSem.Fs`, the twin of `theories/LinuxProcessSem/Fs.v`.
Rocq has no `Checks/Cases` file for `Fs.v`, so this one mirrors no Rocq
source.  Not part of the trusted specification: this file is QA on the
definitions, written to be READ.  Two kinds of claim sit here and each
pin's docstring says which it makes: the file-content pins (`file_read`,
`file_write`, `file_truncate`, `fs_remove` as `unlink`) are claims about
what the kernel does, with the citation beside them; the canonical-form
pins (`path_ltb`, `fs_set`, `fs_sorted`, `valid_fs`'s order and
NUL-in-name clauses, `file_from`) are claims about the MODEL'S
representation, which no syscall observes — the kernel has no byte order
on a flat map — and they cite the model.  The split is by pin, not by
definition: `pin_valid_fs_accepts_nul_in_contents` is a claim about file
DATA and cites the kernel.  The representation is not inert either: the
final image is `ExitEv`'s payload (`State/Model.lean`) and the
equivalence compares it with `=`, so the canonical form is what makes two
runs' images comparable at all.

Only twins of Rocq lemmas stay beside the definitions.  Everything here is
something else: the `fs_remove` lookup laws, which are the general form of
"unlink removes exactly the named entry" and twin no Rocq lemma, the
helpers only they need, and the concrete pins.  Each decision the
definitions take is held to what Linux does on a concrete image, and the
concrete mistake it could have made is refuted beside it.

The paths are single ASCII bytes so the pins read as the names they stand
for: `a` = 97, `b` = 98, `c` = 99. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs

/-! ## Helpers no Rocq twin needs -/

theorem path_eqb_false_of_ne (p q : path) (h : p ≠ q) : path_eqb p q = false := by
  cases hpq : path_eqb p q with
  | false => rfl
  | true => exact absurd ((path_eqb_eq p q).1 hpq) h

theorem bv_ltu_irrefl {n : Nat} (a : BitVec n) : bv_ltu a a = false := by
  cases h : bv_ltu a a with
  | false => rfl
  | true => exact absurd ((bv_ltu_eq_true a a).1 h) (Nat.lt_irrefl _)

theorem path_ltb_irrefl (p : path) : path_ltb p p = false := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [path_ltb, ih, bv_ltu_irrefl, Bool.and_false, Bool.or_false]

/-! ## `fs_remove` removes exactly the named path

Linux's `unlink` drops the one directory entry the last component names
(`do_unlinkat` / `vfs_unlink`, fs/namei.c, Linux v6.18.46): no other
name changes, and a name that merely extends the removed one is a
different entry.  The two theorems state that against the map for every
`Fs`: every OTHER key still answers what it answered before, and, on the
canonical form, the named key is gone.  The second needs sortedness only
because an unsorted list could carry a key twice; the pins below
exercise both on concrete images. -/

theorem fs_lookup_cons_ne (k : path) (d : List byte) (r : Fs) (q : path)
    (h : q ≠ k) : fs_lookup ((k, d) :: r) q = fs_lookup r q := by
  simp only [fs_lookup]
  rw [path_eqb_false_of_ne q k h]
  simp only [Bool.false_eq_true, ↓reduceIte]

theorem fs_remove_lookup_other (fs : Fs) (p q : path) (hne : q ≠ p) :
    fs_lookup (fs_remove fs p) q = fs_lookup fs q := by
  induction fs with
  | nil => rfl
  | cons kd r ih =>
    obtain ⟨k, d⟩ := kd
    simp only [fs_remove]
    cases hpk : path_eqb p k with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, fs_lookup]
      rw [ih]
    | true =>
      simp only [↓reduceIte]
      have hk : p = k := (path_eqb_eq p k).1 hpk
      subst hk
      exact (fs_lookup_cons_ne p d r q hne).symm

/-- On a sorted list a key below the head is below every key, so it is
absent. -/
theorem fs_lookup_none_of_lt_head (fs : Fs) (a : path) :
    fs_sorted fs = true → fs_lt_head a fs = true → fs_lookup fs a = none := by
  induction fs with
  | nil => intro _ _; rfl
  | cons qd r ih =>
    obtain ⟨q, d⟩ := qd
    intro hs hh
    rw [fs_sorted_cons, Bool.and_eq_true] at hs
    obtain ⟨hq, hr⟩ := hs
    have hne : a ≠ q := fun h => by
      subst h
      exact Bool.false_ne_true ((path_ltb_irrefl a).symm.trans hh)
    rw [fs_lookup_cons_ne q d r a hne]
    exact ih hr (fs_lt_head_trans a q r hh hq)

theorem fs_remove_lookup_same (fs : Fs) (p : path) (hs : fs_sorted fs = true) :
    fs_lookup (fs_remove fs p) p = none := by
  induction fs with
  | nil => rfl
  | cons qd r ih =>
    obtain ⟨q, d⟩ := qd
    rw [fs_sorted_cons, Bool.and_eq_true] at hs
    obtain ⟨hq, hr⟩ := hs
    simp only [fs_remove]
    cases hpq : path_eqb p q with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [fs_lookup_cons_ne q d _ p (fun h => Bool.false_ne_true
          (hpq.symm.trans ((path_eqb_eq p q).2 h)))]
      exact ih hr
    | true =>
      simp only [↓reduceIte]
      have hk : p = q := (path_eqb_eq p q).1 hpq
      subst hk
      exact fs_lookup_none_of_lt_head r p hr hq

/-! ## Pins -/

/-- The image `{a ↦ [1], ab ↦ [2], b ↦ [3]}`, in canonical form. -/
def pin_fs : Fs :=
  [([97#8], [1#8]), ([97#8, 98#8], [2#8]), ([98#8], [3#8])]

theorem pin_fs_sorted : fs_sorted pin_fs = true := by decide

/-- Order: a proper prefix sorts first, and the order is strict. -/
theorem pin_prefix_sorts_first : path_ltb [97#8] [97#8, 98#8] = true := by decide
theorem pin_prefix_not_after : path_ltb [97#8, 98#8] [97#8] = false := by decide
theorem pin_unsorted_rejected : fs_sorted [([98#8], [3#8]), ([97#8], [1#8])] = false := by
  decide

/-- Bytes compare UNSIGNED: 0x80 sorts after 0x7f.  A model convention
(`path_ltb` on `bv_ltu`), not a kernel fact — no kernel order on names is
being modeled — pinned so that a signed comparison, which would put every
byte at or above 0x80 first and break `fs_sorted` on every image built
with the unsigned one, cannot slip in. -/
theorem pin_high_byte_sorts_after : path_ltb [0x7f#8] [0x80#8] = true := by decide
theorem pin_high_byte_not_before : path_ltb [0x80#8] [0x7f#8] = false := by decide

/-- `fs_set` replaces in place, inserts at the sorted position, and keeps
the canonical form; it neither prepends nor appends blindly. -/
theorem pin_set_replaces_in_place :
    fs_set pin_fs [97#8] [5#8] = [([97#8], [5#8]), ([97#8, 98#8], [2#8]), ([98#8], [3#8])] := by
  decide
theorem pin_set_does_not_duplicate : fs_set pin_fs [97#8] [5#8] ≠ ([97#8], [5#8]) :: pin_fs := by
  decide
theorem pin_set_inserts_between :
    fs_set pin_fs [97#8, 97#8] [4#8]
      = [([97#8], [1#8]), ([97#8, 97#8], [4#8]), ([97#8, 98#8], [2#8]), ([98#8], [3#8])] := by
  decide
theorem pin_set_inserts_first : fs_set pin_fs [96#8] [4#8] = ([96#8], [4#8]) :: pin_fs := by
  decide
theorem pin_set_does_not_append_first : fs_set pin_fs [96#8] [4#8] ≠ pin_fs ++ [([96#8], [4#8])] := by
  decide

/-- Replacing a key that is not at the HEAD: `b` is the last entry of
`pin_fs`, and `fs_set` walks past `a` and `ab` to replace it in place,
neither prepending a second `b` nor moving it. -/
theorem pin_set_replaces_non_head_in_place :
    fs_set pin_fs [98#8] [5#8] = [([97#8], [1#8]), ([97#8, 98#8], [2#8]), ([98#8], [5#8])] ∧
    fs_set pin_fs [98#8] [5#8] ≠ ([98#8], [5#8]) :: pin_fs := by
  decide

/-- Canonical form has no duplicate keys: `fs_sorted` is STRICT, so an
image listing `a` twice is not sorted, whatever the order of the rest.  A
non-strict port would accept it and `fs_lookup` would silently answer
the first copy. -/
theorem pin_sorted_rejects_duplicate_key :
    fs_sorted [([97#8], [1#8]), ([97#8], [2#8])] = false := by decide

/-- …and the check runs down the WHOLE list, not the first adjacent pair
alone: `a < b` holds but `b < ab` does not, so `[a, b, ab]` is unsorted.
Every other `fs_sorted` fixture has at most two entries or is sorted
throughout, so a port that tested only the head pair passed them all.
`Fs.lean`'s `fs_sorted_cons` refuses that port in the trusted module;
this is the closed witness the pin file carries on its own. -/
theorem pin_sorted_checks_the_tail :
    fs_sorted [([97#8], [1#8]), ([98#8], [3#8]), ([97#8, 98#8], [2#8])] = false := by
  decide
theorem pin_set_appends_last :
    fs_set pin_fs [99#8] [4#8] = pin_fs ++ [([99#8], [4#8])] := by decide
theorem pin_set_does_not_prepend_last : fs_set pin_fs [99#8] [4#8] ≠ ([99#8], [4#8]) :: pin_fs := by
  decide

/-- The NUL-free clause of `valid_fs`: a path holding a NUL byte is no
image a program could name. -/
theorem pin_valid_fs_accepts_image : valid_fs pin_fs := by
  simp only [valid_fs]
  decide
theorem pin_valid_fs_rejects_nul : ¬ valid_fs [([0#8], [])] := fun h =>
  h.2 ([0#8], []) (List.Mem.head _) (List.Mem.head _)

/-- The NUL-free clause is about NAMES, not contents: a file whose data is
a single NUL byte is a valid image.  The kernel puts no restriction on
file data (`write` stores whatever `copy_folio_from_iter_atomic`
delivers, `generic_perform_write`, mm/filemap.c, Linux v6.18.46); a port
that scanned the contents too would refuse every binary file. -/
theorem pin_valid_fs_accepts_nul_in_contents : valid_fs [([97#8], [0#8])] := by
  simp only [valid_fs]
  decide

/-- The two clauses are a CONJUNCTION, the NUL clause over EVERY entry,
and the empty image satisfies both: a NUL-named file beside a clean one
is refused even though the image is sorted (0 < 97), and an unsorted
image is refused even though every name is NUL-free.  `Run.valid_input`
reads `valid_fs`, so a port that dropped the order clause, or wrote the
NUL clause as an existential, would ADMIT an initial image Rocq's
`valid_input` refuses — the widening a canonical-form invariant exists to
prevent — and the existential port would also refuse the empty image,
the base case every validity argument over a chain of `fs_set` rests on.
Every other `valid_fs` fixture is a one-entry image, where all three
ports agree with the definition. -/
theorem pin_valid_fs_empty_image : valid_fs [] := by
  simp only [valid_fs]
  decide
theorem pin_valid_fs_rejects_nul_beside_clean_name :
    ¬ valid_fs [([0#8], []), ([97#8], [1#8])] := by
  simp only [valid_fs]
  decide
theorem pin_valid_fs_rejects_unsorted :
    ¬ valid_fs [([98#8], [3#8]), ([97#8], [1#8])] := by
  simp only [valid_fs]
  decide

/-- `unlink("a")` removes the entry `a` and nothing else: `ab`, which
merely extends the name, and `b` both stay (`do_unlinkat` / `vfs_unlink`,
fs/namei.c, Linux v6.18.46). -/
theorem pin_unlink_removes_only_the_named_path :
    fs_remove pin_fs [97#8] = [([97#8, 98#8], [2#8]), ([98#8], [3#8])] := by decide

/-- Refuted: removing by prefix, which would take `ab` with `a`. -/
theorem pin_unlink_is_not_prefix_removal :
    fs_remove pin_fs [97#8] ≠ [([98#8], [3#8])] := by decide

/-- Refuted: dropping the tail from the named entry onward. -/
theorem pin_unlink_keeps_later_entries :
    fs_remove pin_fs [97#8, 98#8] ≠ [([97#8], [1#8])] := by decide

/-- A name that is not in the image changes nothing: the map is the same,
which is what lets `unlinkat` decide -ENOENT first and remove second. -/
theorem pin_unlink_absent_path_changes_nothing : fs_remove pin_fs [99#8] = pin_fs := by
  decide

/-- The removed name is gone and the others answer as before. -/
theorem pin_unlink_named_gone : fs_lookup (fs_remove pin_fs [97#8]) [97#8] = none := by
  decide
theorem pin_unlink_neighbour_kept :
    fs_lookup (fs_remove pin_fs [97#8]) [97#8, 98#8] = some [2#8] := by decide

/-- `fs_remove` drops the FIRST match only.  On the canonical form there
is no second one, which is why `fs_remove_lookup_same` asks for
`fs_sorted`; this pin refutes a filter that would drop every match. -/
theorem pin_remove_first_match_only :
    fs_remove [([97#8], [1#8]), ([97#8], [2#8])] [97#8] = [([97#8], [2#8])] := by decide

/-- Removal keeps the canonical form (the general statement is
`fs_remove_sorted`). -/
theorem pin_unlink_middle_stays_sorted : fs_sorted (fs_remove pin_fs [97#8, 98#8]) = true := by
  decide

/-- A read short of the requested count stops at end-of-file, and a read
at or past it returns no bytes (`shmem_file_read_iter`, mm/shmem.c,
Linux v6.18.46). -/
theorem pin_read_truncates_at_eof : file_read [1#8, 2#8, 3#8] 1 10 = [2#8, 3#8] := by
  decide
theorem pin_read_at_eof_is_empty : file_read [1#8, 2#8, 3#8] 3 1 = [] := by decide
theorem pin_read_past_eof_is_empty : file_read [1#8, 2#8, 3#8] 5 1 = [] := by decide

/-- An offset an lseek left far past the end still reads nothing: the
walk is charged to the file, not the offset. -/
theorem pin_read_far_past_eof_is_empty :
    file_read [1#8, 2#8] (Z_to_bv 64 (2 ^ 63 - 1)) 1 = [] := by decide

/-- Refuted: zero-padding a short read to the requested count, and
wrapping an out-of-range offset back into the file. -/
theorem pin_read_does_not_zero_pad : file_read [1#8, 2#8, 3#8] 1 3 ≠ [2#8, 3#8, 0#8] := by
  decide
theorem pin_read_does_not_wrap : file_read [1#8, 2#8, 3#8] 5 1 ≠ [1#8] := by decide

theorem pin_file_from_skips : file_from [1#8, 2#8, 3#8] 1 = [2#8, 3#8] := by decide
theorem pin_file_from_past_end : file_from [1#8, 2#8] 5 = [] := by decide

/-- A zero count reads nothing wherever the offset is. -/
theorem pin_read_zero_count : file_read [1#8, 2#8, 3#8] 0 0 = [] := by decide

/-- The arm is `off ≤ 0`, not `off = 0`: a non-positive offset yields the
whole file rather than walking it to nothing.  No register offset is
negative (`bv_unsigned`), which is why `file_from_skipn` carries `0 ≤ off`. -/
theorem pin_file_from_negative_offset : file_from [1#8, 2#8] (-1) = [1#8, 2#8] := by decide

/-- A zero-length write past end-of-file leaves the file as it was
(`generic_write_checks_count`, fs/read_write.c, Linux v6.18.46:
`if (!*count) return 0;` before the `IOCB_APPEND` repositioning). -/
theorem pin_zero_length_write_is_noop : file_write [97#8] 5 [] = [97#8] := by decide

/-- Refuted: zero-extending the file out to the offset on a zero-length
write. -/
theorem pin_zero_length_write_does_not_extend :
    file_write [97#8] 5 [] ≠ [97#8, 0#8, 0#8, 0#8, 0#8] := by decide

/-- A nonempty write past end-of-file leaves a hole that reads back as
zeros. -/
theorem pin_sparse_write_zero_fills : file_write [97#8] 3 [98#8] = [97#8, 0#8, 0#8, 98#8] := by
  decide

/-- Refuted: appending at the old end instead of at the offset. -/
theorem pin_sparse_write_is_not_append : file_write [97#8] 3 [98#8] ≠ [97#8, 98#8] := by
  decide

/-- A write ending exactly at end-of-file, and one that starts inside the
file and runs past its end: the bytes land at the offset and the file
grows by the overhang, no more and no less. -/
theorem pin_write_at_eof_appends : file_write [97#8] 1 [98#8] = [97#8, 98#8] := by decide
theorem pin_write_straddling_eof :
    file_write [1#8, 2#8, 3#8] 2 [9#8, 9#8] = [1#8, 2#8, 9#8, 9#8] := by decide
theorem pin_write_straddling_eof_is_not_clipped :
    file_write [1#8, 2#8, 3#8] 2 [9#8, 9#8] ≠ [1#8, 2#8, 9#8] := by decide
theorem pin_write_straddling_eof_is_not_insert :
    file_write [1#8, 2#8, 3#8] 2 [9#8, 9#8] ≠ [1#8, 2#8, 9#8, 9#8, 3#8] := by decide

/-- A write inside the file overwrites in place; it does not insert. -/
theorem pin_write_overwrites :
    file_write [1#8, 2#8, 3#8, 4#8] 1 [9#8, 9#8] = [1#8, 9#8, 9#8, 4#8] := by decide
theorem pin_write_does_not_insert :
    file_write [1#8, 2#8, 3#8, 4#8] 1 [9#8, 9#8] ≠ [1#8, 9#8, 9#8, 2#8, 3#8, 4#8] := by
  decide

/-- `ftruncate` to a longer length zero-fills.  On tmpfs, where the
harness's files live, a grow writes ONLY the size: `shmem_setattr`
(mm/shmem.c, Linux v6.18.46, commit 1f99e9ab748f) does
`i_size_write(inode, newsize)` and touches the page cache only under
`if (newsize <= oldsize)`; `truncate_setsize` (mm/truncate.c) is not on
tmpfs's path at all.  The grown region reads as zeros for two reasons:
an index with no folio is copied from `ZERO_PAGE(0)` by
`shmem_file_read_iter` (mm/shmem.c, Linux v6.18.46), and the bytes past the old EOF in
the last cached folio were zeroed when it was first filled
(`shmem_write_end`, mm/shmem.c, v6.18.46, through include/linux/highmem.h's
`folio_zero_segments`) or when a shrink
cut it (`shmem_undo_range` → `truncate_inode_partial_folio`,
mm/truncate.c, → `folio_zero_range`, include/linux/highmem.h:668, v6.18.46).  On a
filesystem that does call `truncate_setsize`, the grow path is
`pagecache_isize_extended` (mm/truncate.c), which zeroes only the tail of
a straddling folio on a sub-page block size (`if (from >= to || bsize >=
PAGE_SIZE) return;`) and leaves the rest to the read side; it is not
`truncate_inode_partial_folio`, which zeroes at and past the NEW size.
To a shorter length drops the tail; to the same length changes
nothing. -/
theorem pin_truncate_grow_zero_fills : file_truncate [97#8] 3 = [97#8, 0#8, 0#8] := by decide
theorem pin_truncate_shrink_drops_tail : file_truncate [1#8, 2#8, 3#8] 1 = [1#8] := by decide
theorem pin_truncate_same_length : file_truncate [1#8, 2#8] 2 = [1#8, 2#8] := by decide
theorem pin_truncate_to_zero : file_truncate [1#8, 2#8] 0 = [] := by decide
theorem pin_truncate_to_zero_keeps_nothing : file_truncate [1#8, 2#8] 0 ≠ [1#8] := by decide
theorem pin_truncate_same_length_is_not_grow : file_truncate [1#8, 2#8] 2 ≠ [1#8, 2#8, 0#8] := by
  decide

/-- Refuted: a grow that leaves the length alone, and a shrink that keeps
the dropped bytes. -/
theorem pin_truncate_grow_is_not_noop : file_truncate [97#8] 3 ≠ [97#8] := by decide
theorem pin_truncate_shrink_is_not_noop : file_truncate [1#8, 2#8, 3#8] 1 ≠ [1#8, 2#8, 3#8] := by
  decide


end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs
