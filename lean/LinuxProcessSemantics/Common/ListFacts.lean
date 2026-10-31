/-! rocq-baseline: 2cde689f94c086b868999970834b76a25616b94a -/

/-! # Common.ListFacts — generic list facts

Ported from `theories/Common/ListFacts.v` at the baseline above: its
lemmas, with the Rocq statements.  The Rocq file is the single home for
list facts the examples used to re-prove under several names, and its
proofs defer to stdpp's list library; the proofs here use core's `List`
lemmas.  Like the Rocq file, this module imports no other
`Common` module.

Spellings: Rocq `firstn`/`skipn` are `List.take`/`List.drop`, `nth i l d`
is `l.getD i d` (as in `Common.SymExec`), `In x l` is `x ∈ l`, and `S i`
is `i + 1`.  `firstn_S_nth` keeps Rocq's explicit type argument, for its
call sites' argument order `(A l i d)`.

Universes: Rocq's `A` may be a proposition such as `True` and has an upper
bound; Lean's `A : Type u` may not be a proposition and has no upper bound. -/

namespace LinuxProcessSemantics.Common.ListFacts

universe u

/-- Peel the last element off a `take (i + 1)`. -/
theorem firstn_S_nth (A : Type u) (l : List A) (i : Nat) (d : A) (hi : i < l.length) :
    l.take (i + 1) = l.take i ++ [l.getD i d] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact (List.take_append_getElem hi).symm

/-- Membership in a prefix implies membership in the whole list. -/
theorem In_firstn {A : Type u} (x : A) (n : Nat) (l : List A) (h : x ∈ l.take n) : x ∈ l :=
  List.mem_of_mem_take h

/-- Expose the head of a `drop i`. -/
theorem skipn_cons_nth {A : Type u} (l : List A) (i : Nat) (d : A) (hi : i < l.length) :
    l.drop i = l.getD i d :: l.drop (i + 1) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.drop_eq_getElem_cons hi

/-- `take` of a list's full length is the list. -/
theorem firstn_all_len {A : Type u} (l : List A) : l.take l.length = l :=
  List.take_length

-- Each theorem restates its lemma with `A` in a universe `w` the line declares,
-- so it builds only while `A`'s universe is a parameter of the lemma. The
-- testing/lean-mutations cases `common-firstn-S-nth-universe-zero`,
-- `common-In-firstn-universe-zero`, `common-skipn-cons-nth-universe-zero`, and
-- `common-firstn-all-len-universe-zero` narrow the binder to `Type` and expect
-- the restatement to fail (docs/lean-port/BRIEF.md section 3, "Universes").
universe w in
theorem firstn_S_nth_any_universe : ∀ (A : Type w) (l : List A) (i : Nat) (d : A),
    i < l.length → l.take (i + 1) = l.take i ++ [l.getD i d] :=
  firstn_S_nth

universe w in
theorem In_firstn_any_universe : ∀ {A : Type w} (x : A) (n : Nat) (l : List A),
    x ∈ l.take n → x ∈ l :=
  In_firstn

universe w in
theorem skipn_cons_nth_any_universe : ∀ {A : Type w} (l : List A) (i : Nat) (d : A),
    i < l.length → l.drop i = l.getD i d :: l.drop (i + 1) :=
  skipn_cons_nth

universe w in
theorem firstn_all_len_any_universe : ∀ {A : Type w} (l : List A), l.take l.length = l :=
  firstn_all_len

-- Each lemma at an element type above `Type 0`, a list of types.
example (l : List Type) (i : Nat) (hi : i < l.length) :
    l.take (i + 1) = l.take i ++ [l.getD i Unit] :=
  firstn_S_nth Type l i Unit hi
example (x : Type) (l : List Type) (h : x ∈ l.take 2) : x ∈ l :=
  In_firstn x 2 l h
example (l : List Type) (i : Nat) (hi : i < l.length) :
    l.drop i = l.getD i Unit :: l.drop (i + 1) :=
  skipn_cons_nth l i Unit hi
example (l : List Type) : l.take l.length = l :=
  firstn_all_len l
-- And at `Type 0`, a list of bytes.
example (s : List (BitVec 8)) (i : Nat) (hi : i < s.length) :
    s.take (i + 1) = s.take i ++ [s.getD i 0] :=
  firstn_S_nth (BitVec 8) s i 0 hi
example (x : BitVec 8) (s : List (BitVec 8)) (n : Nat) (h : x ∈ s.take n) : x ∈ s :=
  In_firstn x n s h
example (s : List (BitVec 8)) (i : Nat) (hi : i < s.length) :
    s.drop i = s.getD i 0 :: s.drop (i + 1) :=
  skipn_cons_nth s i 0 hi
example (s : List (BitVec 8)) : s.take s.length = s :=
  firstn_all_len s
-- Rocq's A may be a proposition such as True, by cumulativity (the header);
-- Lean's binder A : Type _ refuses one. The docstring is the whole expected
-- error, so a different failure (an unknown name, a reordered argument) fails
-- the #guard_msgs.
/-- error: Application type mismatch: The argument
  True
has type
  Prop
of sort `Type` but is expected to have type
  Type _
of sort `Type (_ + 1)` in the application
  firstn_S_nth True -/
#guard_msgs in
set_option pp.mvars false in
example := @firstn_S_nth True

/-- error: Application type mismatch: The argument
  True
has type
  Prop
of sort `Type` but is expected to have type
  Type _
of sort `Type (_ + 1)` in the application
  @In_firstn True -/
#guard_msgs in
set_option pp.mvars false in
example := @In_firstn True

/-- error: Application type mismatch: The argument
  True
has type
  Prop
of sort `Type` but is expected to have type
  Type _
of sort `Type (_ + 1)` in the application
  @skipn_cons_nth True -/
#guard_msgs in
set_option pp.mvars false in
example := @skipn_cons_nth True

/-- error: Application type mismatch: The argument
  True
has type
  Prop
of sort `Type` but is expected to have type
  Type _
of sort `Type (_ + 1)` in the application
  @firstn_all_len True -/
#guard_msgs in
set_option pp.mvars false in
example := @firstn_all_len True


end LinuxProcessSemantics.Common.ListFacts
