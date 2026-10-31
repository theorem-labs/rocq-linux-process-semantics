import LinuxProcessSemantics.Common.DrainSim
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Examples.tail1_ns.SourceMemImage
import LinuxProcessSemantics.Examples.tail1_ns.TargetMemImage
import LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_code
/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # tail1-ns: shared helpers for the two per-binary drain proofs.

PROOF-SIDE FILE (not part of the trusted specification).

Both binaries implement tail-1: read all of stdin to EOF in 1024-byte
chunks, folding each byte through the newline/append logic that tracks
the current unterminated line `cur` and the last completed line `done`
(with its trailing '\n'); at EOF write the last line (cur if nonempty,
else done, else nothing) in one write and exit 0. A line exceeding
4096 bytes aborts with exit 3.

This file fixes the shared abstract model (`A`, `f`, `out`, `ec`) that
both per-binary proofs fold onto, the image probes, memory read-back
helpers, value facts, and the DrainSim record entry-point lemmas.

Conventions: bytes are `byte = bv 8`, machine values `word = bv 64`;
unbounded address bookkeeping is in `Int` over `bv_unsigned`; computed
stack addresses use the canonical `Z_to_bv 64 (...)` form, pc values
the numeral-literal form. -/

namespace LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_defs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.DrainSim
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Common.ImageBytes
open LinuxProcessSemantics.Examples.tail1_ns.SourceMemImage
open LinuxProcessSemantics.Examples.tail1_ns.TargetMemImage
open LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_code

/-- Abstract fold state: `(cur, done)` — the current unterminated line and
the last completed line (including its trailing '\n'). The concrete
counters `cur_n`/`done_n` are the list lengths. -/
def A : Type := List byte × List byte

/-- Per-byte step. A '\n' (=10) closes the current line into `done` and
resets `cur`; otherwise a line already at 4096 bytes aborts (`none`),
else the byte is appended to `cur`. -/
def f (a : A) (b : byte) : Option A :=
  let (cur, done) := a
  if bv_eqb b (Z_to_bv 8 10) then some ([], cur ++ [Z_to_bv 8 10])
  else if 4096 ≤ (cur.length : Int) then none
       else some (cur ++ [b], done)

/-- At EOF: emit `cur` if nonempty, else `done`, else nothing. -/
def out (a : A) : List byte :=
  let (cur, done) := a
  match cur with | [] => done | _ => cur

/-- The emitted line always fits in one modeled write
(`CatSim.buf_modeled`, far below `Uaccess.rw_bytes_max`). Both cases
are capped by the fold itself: `f` refuses a 4097th byte of `cur`,
and `done` is a closed line plus its '\n'. Stated over the caps the
per-binary invariants carry rather than over every abstract state, so
`out` stays the plain projection it was. -/
theorem out_modeled (cur done : List byte)
    (Hc : (cur.length : Int) ≤ 4096) (Hd : (done.length : Int) ≤ 4097) :
    buf_modeled (out (cur, done)) := by
  cases cur with
  | nil => simp only [buf_modeled, out, rw_bytes_max]; omega
  | cons b bs => simp only [buf_modeled, out, rw_bytes_max]; omega

/-- Line-too-long exit code. -/
def ec : word := Z_to_bv 64 3

/-- Initial abstract state: both buffers empty. -/
def a0 : A := ([], [])

theorem ec_lt256 : bv_unsigned ec < 256 := by decide

/-- The wrapping word/nat offset add in the canonical `Z_to_bv` form
(hypothesis-free: both sides wrap identically). -/
theorem word_to_nat_ntw (n : Nat) (Hn : (n : Int) < 2 ^ 64) :
    word_to_nat (nat_to_word n) = n := by
  unfold word_to_nat
  have h := u_ntw n Hn
  unfold bv_unsigned at h
  omega

/-- The low byte of a zero-extended byte is the byte back (the store
normal form after an `lbu`/`sb` round-trip). -/
theorem byte_low_zext (b : byte) :
    Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) = b := by
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, u_zext8]
  have h := u8_range b
  change bv_unsigned b % 256 = bv_unsigned b
  exact Int.emod_eq_of_lt h.1 h.2

/-- The machine's newline test on the zero-extended loaded byte IS the
abstract byte-level test. -/
theorem c_eq_zext10 (b : byte) :
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 10) = bv_eqb b (Z_to_bv 8 10) := by
  unfold c_eq bv_eqb
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    apply bv_eq_of_unsigned
    have hu := congrArg bv_unsigned h
    rw [u_zext8] at hu
    exact hu
  · intro h
    apply bv_eq_of_unsigned
    rw [u_zext8, h]
    rfl

theorem bv_ltu_ltb (x y : word) :
    bv_ltu x y = decide (bv_unsigned x < bv_unsigned y) := c_ltu_ltb x y

theorem c_ltu_x0 (x : word) : c_ltu x (Z_to_bv 64 0) = false := by
  rw [c_ltu_ltb]
  change decide (bv_unsigned x < 0) = false
  have hx := u64_range x
  exact decide_eq_false (by omega)

/-- Count comparisons over `nat_to_word` as Z comparisons. -/
theorem c_eq_ntw (m n : Nat) (Hm : (m : Int) < 2 ^ 64)
    (Hn : (n : Int) < 2 ^ 64) :
    c_eq (nat_to_word m) (nat_to_word n) = decide ((m : Int) = (n : Int)) := by
  unfold c_eq bv_eqb
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have hu := congrArg bv_unsigned h
    rw [u_ntw m Hm, u_ntw n Hn] at hu
    exact hu
  · intro h
    apply bv_eq_of_unsigned
    rw [u_ntw m Hm, u_ntw n Hn, h]

theorem c_lts_ntw (m n : Nat) (Hm : (m : Int) < 2 ^ 63)
    (Hn : (n : Int) < 2 ^ 63) :
    c_lts (nat_to_word m) (nat_to_word n) = decide ((m : Int) < (n : Int)) := by
  rw [c_lts_small _ _ (by rw [u_ntw m (by omega)]; exact Hm)
    (by rw [u_ntw n (by omega)]; exact Hn)]
  rw [bv_ltu_ltb, u_ntw m (by omega), u_ntw n (by omega)]

theorem c_eq_sub_self (x : word) : c_eq (v_sub x x) (Z_to_bv 64 0) = true := by
  apply c_eq_0_of_u
  unfold v_sub
  rw [Int.sub_self]
  rfl

/-- Loop-counter decrement over `nat_to_word`. -/
theorem v_addi_ntw_pred (n : Nat) (Hn : 0 < n) (Hb : (n : Int) < 2 ^ 64) :
    v_addi (nat_to_word n) (-1) = nat_to_word (n - 1) := by
  apply bv_eq_of_unsigned
  unfold v_addi
  rw [u_ntw n Hb]
  unfold nat_to_word
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned]
  congr 1
  omega

/-- Pointer increment: `addi p,p,1` advances a pointer-plus-index by
one index step (hypothesis-free: both sides are the same wrap;
same bridge as grep_args_ns's local `v_addi_ptr_S`). -/
theorem v_addi_ptr_S (p : word) (j : Nat) :
    v_addi (p + nat_to_word j) 1 = p + nat_to_word (Nat.succ j) := by
  rw [show v_addi (p + nat_to_word j) 1 =
      (p + nat_to_word j) + nat_to_word 1 from (word_add_nat _ 1).symm]
  rw [nat_to_word_add_merge]

/-- `base + nat_to_word j` against the machine's `add rs_count rs_base`
operand order (`v_add` with the count FIRST — the one reversed add in
the source's copy loop). -/
theorem word_add_nat_comm (a : word) (n : Nat) (Hn : (n : Int) < 2 ^ 64) :
    a + nat_to_word n = v_add (nat_to_word n) a := by
  rw [word_add_nat]
  unfold v_add
  rw [u_ntw n Hn]
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned]
  congr 1
  omega

theorem source_init_pc_val : SourceMemImage_init_pc = 0x11154 := by rfl

theorem target_init_pc_val : TargetMemImage_init_pc = 0x1001190 := by rfl

/-- Store targets at/above the end of the (page-rounded) source rodata
segment avoid all read-only segments (the rw data segment is exempt).
After the `-z separate-code` relink there are THREE read-only
segments — r-- headers/.riscv.attributes `[0x10000, 0x11000)`, r-x
text `[0x11000, 0x12000)` and r-- .eh_frame `[0x12000, 0x13000)` — so
the rw- data segment, and the first writable address, start at
0x13000. -/
theorem source_avoids_ro (a : word) (n : Int) (Ha : 0x13000 ≤ bv_unsigned a) :
    range_avoids_ro_segs source_segs (bv_unsigned a) n = true := by
  exact range_avoids_ro_above source_segs 0x13000 (bv_unsigned a) n (by decide) Ha

/-! The generated `_chars_eq` proves by reflexivity that a string literal equals
`String.ofList (List.replicate 24576 '0')`. Nanoda compares the literal's expansion with
recursive unfolding of `List.replicate`, using a stack frame per character; this overflows
its default 8 MiB stack.

The bridge uses exactly the flat term nanoda builds when expanding a string literal:
`String.ofList` of `@List.cons.{0} Char (Char.ofNat n) ... (@List.nil.{0} Char)`.
See nanoda_lib's `str_lit_to_constructor` in `src/expr.rs` at commit
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`. Its `alloc_expr` in `src/util.rs` at the same
commit first looks up a term among the exported terms, so checking the bridge compares
pointers instead of recursing over the characters. Raw natural literals preserve that
exact constructor representation.

The bridge is added with `addDecl`: elaborating `rfl` for this statement unfolds the
literal and exhausts the elaborator's heartbeats (measured with Lean v4.34.0). The
kernel checks each declaration as it is added. Then `tail1_rep_check` turns the flat list
into `List.replicate 24576 '0'` with one `decide +kernel` per certificate. -/

/-- Build the term nanoda's `str_lit_to_constructor` expands a string literal to. -/
def tail1_flat_chars (s : String) : Lean.Expr := Id.run do
  let charE := Lean.mkConst ``Char
  let consE := Lean.mkApp (Lean.mkConst ``List.cons [Lean.Level.zero]) charE
  let mut acc := Lean.mkApp (Lean.mkConst ``List.nil [Lean.Level.zero]) charE
  for c in s.toList.reverse do
    acc := Lean.mkApp2 consE
      (Lean.mkApp (Lean.mkConst ``Char.ofNat) (Lean.mkRawNatLit c.toNat)) acc
  return acc

/-- Add a flat character definition and its kernel-checked bridge from a literal. -/
elab (name := tail1_flat_bridge) "tail1_flat_bridge " flat:ident bridge:ident
    " from " src:ident : command => do
  let srcName ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo src
  let env ← Lean.getEnv
  let some (.defnInfo d) := env.find? srcName | throwError "not a def"
  let .lit (.strVal s) := d.value | throwError "not a string literal"
  let ns ← Lean.getCurrNamespace
  let flatName := ns ++ flat.getId
  let listChar := Lean.mkApp (Lean.mkConst ``List [Lean.Level.zero]) (Lean.mkConst ``Char)
  let dv : Lean.DefinitionVal := {
    name := flatName, levelParams := [], type := listChar, value := tail1_flat_chars s,
    hints := .opaque, safety := .safe }
  Lean.Elab.Command.liftCoreM <| Lean.addDecl (.defnDecl dv)
  let lhs := Lean.mkConst srcName
  let rhs := Lean.mkApp (Lean.mkConst ``String.ofList) (Lean.mkConst flatName)
  let ty := Lean.mkApp3 (Lean.mkConst ``Eq [Lean.Level.succ Lean.Level.zero])
    (Lean.mkConst ``String) lhs rhs
  let pf := Lean.mkApp2 (Lean.mkConst ``Eq.refl [Lean.Level.succ Lean.Level.zero])
    (Lean.mkConst ``String) lhs
  let tv : Lean.TheoremVal := {
    name := ns ++ bridge.getId, levelParams := [], type := ty, value := pf }
  Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl tv)

set_option maxRecDepth 100000 in
tail1_flat_bridge tail1_src_seg3_flat tail1_src_seg3_bridge from SourceMemImage_seg_bytes_003

set_option maxRecDepth 100000 in
tail1_flat_bridge tail1_tgt_seg2_flat tail1_tgt_seg2_bridge from TargetMemImage_seg_bytes_002

/-- Expose the source bytes in the constructor form nanoda interns. -/
add_decl_doc tail1_src_seg3_flat

/-- Let nanoda check the source literal through shared constructor terms. -/
add_decl_doc tail1_src_seg3_bridge

/-- Expose the target bytes in the constructor form nanoda interns. -/
add_decl_doc tail1_tgt_seg2_flat

/-- Let nanoda check the target literal through shared constructor terms. -/
add_decl_doc tail1_tgt_seg2_bridge

/-- Check repetition without unfolding the recursive construction of a replicated list. -/
def tail1_rep_check (c : Char) : List Char → Nat → Bool
  | [], n => n == 0
  | _ :: _, 0 => false
  | d :: ds, n + 1 => d == c && tail1_rep_check c ds n

/-- A successful repetition check gives the compact replicated representation. -/
theorem tail1_eq_replicate_of_check (c : Char) :
    ∀ (l : List Char) (n : Nat), tail1_rep_check c l n = true → l = List.replicate n c
  | [], n, h => by
      simp only [tail1_rep_check, beq_iff_eq] at h
      rw [h]
      rfl
  | _ :: _, 0, h => by
      simp only [tail1_rep_check, Bool.false_eq_true] at h
  | d :: ds, n + 1, h => by
      simp only [tail1_rep_check, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, tail1_eq_replicate_of_check c ds n h.2]
      rfl

set_option maxRecDepth 100000 in
/-- Certify the source's flat bytes by kernel reduction. -/
theorem tail1_src_seg3_check : tail1_rep_check '0' tail1_src_seg3_flat 24576 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Certify the target's flat bytes by kernel reduction. -/
theorem tail1_tgt_seg2_check : tail1_rep_check '0' tail1_tgt_seg2_flat 24576 = true := by
  decide +kernel

/-- Connect the source bytes to the generated character representation via the certificate. -/
theorem tail1_src_seg3_chars_eq :
    SourceMemImage_seg_bytes_003 = String.ofList SourceMemImage_seg_bytes_003_chars := by
  rw [tail1_src_seg3_bridge, tail1_eq_replicate_of_check '0' _ _ tail1_src_seg3_check]
  rfl

/-- Connect the target bytes to the generated character representation via the certificate. -/
theorem tail1_tgt_seg2_chars_eq :
    TargetMemImage_seg_bytes_002 = String.ofList TargetMemImage_seg_bytes_002_chars := by
  rw [tail1_tgt_seg2_bridge, tail1_eq_replicate_of_check '0' _ _ tail1_tgt_seg2_check]
  rfl

/-! The generated `SF_` and `TF_` fetch lemmas read their four bytes with
`ascii_segment_read_bytes`, whose `ascii_segment_byte_at` and `hex_chars_byte_at` compare each
offset with the length of the segment's character list before indexing it. In the target,
whose generated character list is a chain of appends and replicates, those lemmas dominated
the replay of the whole closure in both kernels (measured with Lean v4.34.0 and nanoda_lib
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`). `tail1_hex_read` reads the same bytes after one
`List.drop`, never computing a length, and `tail1_ascii_read_eq` proves that the two readers
agree on a one-chunk segment. Each text segment goes through a flat bridge, so the drop walks
constructor cells instead of unfolding appends. -/

/-- Decode the byte whose two hex digits head a character list. -/
def tail1_hex_pair : List Char → Option byte
  | [] => none
  | [_] => none
  | c0 :: c1 :: _ =>
    let h := hex_nybble c0.toUInt8
    let l := hex_nybble c1.toUInt8
    if h < 16 ∧ l < 16 then some (Z_to_bv 8 ((h * 16 + l : Nat) : Int)) else none

/-- Read `n` hex-encoded bytes from the head of a character list. -/
def tail1_hex_read (cs : List Char) : Nat → Option (List byte)
  | 0 => some []
  | n + 1 =>
    match tail1_hex_pair cs with
    | none => none
    | some b =>
      match tail1_hex_read (cs.drop 2) n with
      | none => none
      | some bs => some (b :: bs)

/-- The `i`th hex byte of a list is the pair heading its `2 * i`th suffix. -/
theorem tail1_hex_pair_drop (cs : List Char) (i : Nat) :
    hex_chars_byte_at cs i = tail1_hex_pair (cs.drop (2 * i)) := by
  induction i generalizing cs with
  | zero =>
    match cs with
    | [] => rfl
    | [_] => rfl
    | c0 :: c1 :: rest =>
      unfold hex_chars_byte_at
      rw [dite_eq_left (by simp only [List.length_cons]; omega)]
      rfl
  | succ i ih =>
    match cs with
    | [] => rfl
    | [_] => rfl
    | c0 :: c1 :: rest =>
      rw [show List.drop (2 * (i + 1)) (c0 :: c1 :: rest) = List.drop (2 * i) rest from rfl,
        ← ih rest]
      unfold hex_chars_byte_at
      by_cases h : 2 * i + 1 < rest.length
      · rw [dite_eq_left (by simp only [List.length_cons]; omega), dite_eq_left h]
        rfl
      · rw [dite_eq_right (by simp only [List.length_cons]; omega), dite_eq_right h]

/-- On a one-chunk segment the generated reader and `tail1_hex_read` agree. -/
theorem tail1_ascii_read_eq (cs : List Char) (off n : Nat) :
    ascii_segment_read_bytes [cs] off n = tail1_hex_read (cs.drop (2 * off)) n := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih =>
    have hb : ascii_segment_byte_at [cs] off = tail1_hex_pair (cs.drop (2 * off)) := by
      rw [← tail1_hex_pair_drop]
      simp only [ascii_segment_byte_at]
      split
      · rfl
      · unfold hex_chars_byte_at
        rw [dite_eq_right (by omega)]
    have hd : (cs.drop (2 * off)).drop 2 = cs.drop (2 * (off + 1)) := by
      rw [List.drop_drop]
      congr 1
    simp only [ascii_segment_read_bytes, tail1_hex_read, hb, hd, ih]
    rfl

set_option maxRecDepth 100000 in
tail1_flat_bridge tail1_src_seg1_flat tail1_src_seg1_bridge from SourceMemImage_seg_bytes_001

set_option maxRecDepth 100000 in
tail1_flat_bridge tail1_tgt_seg1_flat tail1_tgt_seg1_bridge from TargetMemImage_seg_bytes_001

/-- Expose the source text in the constructor form nanoda interns. -/
add_decl_doc tail1_src_seg1_flat

/-- Let nanoda check the source text literal through shared constructor terms. -/
add_decl_doc tail1_src_seg1_bridge

/-- Expose the target text in the constructor form nanoda interns. -/
add_decl_doc tail1_tgt_seg1_flat

/-- Let nanoda check the target text literal through shared constructor terms. -/
add_decl_doc tail1_tgt_seg1_bridge

set_option maxRecDepth 100000 in
/-- Every character of the source text is one UTF-8 byte. -/
theorem tail1_src_seg1_ascii : tail1_src_seg1_flat.all (fun c => c.utf8Size == 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Every character of the target text is one UTF-8 byte. -/
theorem tail1_tgt_seg1_ascii : tail1_tgt_seg1_flat.all (fun c => c.utf8Size == 1) = true := by
  decide +kernel

/-- Read the source text segment through its flat characters. -/
theorem tail1_src_seg1_read (off n : Nat) :
    segment_read_bytes SourceMemImage_segment_001.seg_bytes off n =
      tail1_hex_read (tail1_src_seg1_flat.drop (2 * off)) n := by
  change segment_read_bytes [SourceMemImage_seg_bytes_001] off n = _
  rw [tail1_src_seg1_bridge, ← tail1_ascii_read_eq]
  refine segment_read_bytes_ascii [tail1_src_seg1_flat] ?_ off n
  intro cs h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl
  exact tail1_src_seg1_ascii

/-- Read the target text segment through its flat characters. -/
theorem tail1_tgt_seg1_read (off n : Nat) :
    segment_read_bytes TargetMemImage_segment_001.seg_bytes off n =
      tail1_hex_read (tail1_tgt_seg1_flat.drop (2 * off)) n := by
  change segment_read_bytes [TargetMemImage_seg_bytes_001] off n = _
  rw [tail1_tgt_seg1_bridge, ← tail1_ascii_read_eq]
  refine segment_read_bytes_ascii [tail1_tgt_seg1_flat] ?_ off n
  intro cs h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl
  exact tail1_tgt_seg1_ascii

/-- Fetch a source instruction from the text segment through `tail1_hex_read`. -/
theorem tail1_src_fetch (pc : word) (b0 b1 b2 b3 : byte)
    (ha : bv_unsigned pc % 2 = 0)
    (hf : find_segment source_segs (bv_unsigned pc) (↑(4 : Nat)) =
      some SourceMemImage_segment_001)
    (hb : tail1_hex_read (tail1_src_seg1_flat.drop
      (2 * (bv_unsigned pc - SourceMemImage_segment_001.seg_base).toNat)) 4 =
      some [b0, b1, b2, b3]) :
    fetch_word source_segs pc = some (le4 b3 b2 b1 b0) :=
  fetch_word_of_bytes source_segs SourceMemImage_segment_001 pc b0 b1 b2 b3 ha hf
    (by decide +kernel) (by decide +kernel) ((tail1_src_seg1_read _ 4).trans hb)

/-- Fetch a target instruction from the text segment through `tail1_hex_read`. -/
theorem tail1_tgt_fetch (pc : word) (b0 b1 b2 b3 : byte)
    (ha : bv_unsigned pc % 2 = 0)
    (hf : find_segment target_segs (bv_unsigned pc) (↑(4 : Nat)) =
      some TargetMemImage_segment_001)
    (hb : tail1_hex_read (tail1_tgt_seg1_flat.drop
      (2 * (bv_unsigned pc - TargetMemImage_segment_001.seg_base).toNat)) 4 =
      some [b0, b1, b2, b3]) :
    fetch_word target_segs pc = some (le4 b3 b2 b1 b0) :=
  fetch_word_of_bytes target_segs TargetMemImage_segment_001 pc b0 b1 b2 b3 ha hf
    (by decide +kernel) (by decide +kernel) ((tail1_tgt_seg1_read _ 4).trans hb)

/-- The source image's WRITABLE window: the rw- segment covers
`[0x13000, 0x16000)` and the snapshot carries a byte for every address in
it (.bss is zero-filled in the .hex), so `wview` is defined there
whatever the overlay holds — a store into .data/.bss needs no
prior write. That is the `store_ok` side condition machine stores
now carry; stack targets go through the RLIMIT_STACK window
(`solve_store_ok`) instead. -/
theorem source_data_wseg : wseg_ok source_segs (0x13000 : word) 12288 = true := by
  apply wseg_ok_backed source_segs SourceMemImage_segment_003 _ _
    [SourceMemImage_seg_bytes_003_chars]
  · simp only [wseg_cover, source_segs, Source.loaded_segments,
      SourceMemImage_loaded_segments,
      (show SourceMemImage_segment_000.seg_base = 0x10000 from rfl),
      (show SourceMemImage_segment_000.seg_size = 0x1000 from rfl),
      (show SourceMemImage_segment_001.seg_base = 0x11000 from rfl),
      (show SourceMemImage_segment_001.seg_size = 0x1000 from rfl),
      (show SourceMemImage_segment_002.seg_base = 0x12000 from rfl),
      (show SourceMemImage_segment_002.seg_size = 0x1000 from rfl),
      (show SourceMemImage_segment_003.seg_base = 0x13000 from rfl),
      (show SourceMemImage_segment_003.seg_size = 0x3000 from rfl),
      bv_unsigned, BitVec.reduceToNat, Int.cast_ofNat_Int, Int.reduceAdd,
      Int.reduceLT, Int.reduceLE, and_true, and_false, ite_true, ite_false]
  · decide +kernel
  · exact congrArg (fun x => [x]) tail1_src_seg3_chars_eq
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    exact SourceMemImage_seg_bytes_003_ascii
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    exact SourceMemImage_seg_bytes_003_hex
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    simp only [SourceMemImage_seg_bytes_003_chars, List.length_replicate]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      SourceMemImage_seg_bytes_003_chars, List.length_replicate]
    decide +kernel
  · decide +kernel

theorem source_store_ok (m : word → Option byte) (a : word) (n : Nat)
    (Hlo : 0x13000 ≤ bv_unsigned a) (Hhi : bv_unsigned a + (n : Int) ≤ 0x16000) :
    store_ok source_segs m a n = true := by
  exact store_ok_window source_segs m 0x13000 a 12288 n 0x13000 0x16000
    (by decide) (by decide) (by omega) source_data_wseg Hlo Hhi

/-- Target: two read-only (page-rounded) segments ending at 0x1001000
and 0x1002000. -/
theorem target_avoids_ro (a : word) (n : Int) (Ha : 0x1002000 ≤ bv_unsigned a) :
    range_avoids_ro_segs target_segs (bv_unsigned a) n = true := by
  simp only [range_avoids_ro_segs, target_segs, Target.loaded_segments,
    TargetMemImage_loaded_segments, List.all_cons, List.all_nil]
  change ((false || !((0x1000000 : Int) < bv_unsigned a + n &&
      bv_unsigned a < (0x1001000 : Int))) &&
    ((false || !((0x1001000 : Int) < bv_unsigned a + n &&
      bv_unsigned a < (0x1002000 : Int))) && ((true || _) && true))) = true
  have H0 : decide (bv_unsigned a < (0x1001000 : Int)) = false :=
    decide_eq_false (by omega)
  have H1 : decide (bv_unsigned a < (0x1002000 : Int)) = false :=
    decide_eq_false (by omega)
  rw [H0, H1]
  simp only [Bool.and_false, Bool.not_false, Bool.or_true, Bool.true_or, Bool.and_true]

/-- The target image's WRITABLE window: the rw- segment covers
`[0x1002000, 0x1005000)` and the snapshot carries a byte for every address in
it (.bss is zero-filled in the .hex), so `wview` is defined there
whatever the overlay holds — a store into .data/.bss needs no
prior write. That is the `store_ok` side condition machine stores
now carry; stack targets go through the RLIMIT_STACK window
(`solve_store_ok`) instead. -/
theorem target_data_wseg : wseg_ok target_segs (0x1002000 : word) 12288 = true := by
  apply wseg_ok_backed target_segs TargetMemImage_segment_002 _ _
    [TargetMemImage_seg_bytes_002_chars]
  · simp only [wseg_cover, target_segs, Target.loaded_segments,
      TargetMemImage_loaded_segments,
      (show TargetMemImage_segment_000.seg_base = 0x1000000 from rfl),
      (show TargetMemImage_segment_000.seg_size = 0x1000 from rfl),
      (show TargetMemImage_segment_001.seg_base = 0x1001000 from rfl),
      (show TargetMemImage_segment_001.seg_size = 0x1000 from rfl),
      (show TargetMemImage_segment_002.seg_base = 0x1002000 from rfl),
      (show TargetMemImage_segment_002.seg_size = 0x3000 from rfl),
      bv_unsigned, BitVec.reduceToNat, Int.cast_ofNat_Int, Int.reduceAdd,
      Int.reduceLT, Int.reduceLE, and_true, and_false, ite_true, ite_false]
  · decide +kernel
  · exact congrArg (fun x => [x]) tail1_tgt_seg2_chars_eq
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    exact TargetMemImage_seg_bytes_002_ascii
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    exact TargetMemImage_seg_bytes_002_hex
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    simp only [TargetMemImage_seg_bytes_002_chars, List.length_replicate]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      TargetMemImage_seg_bytes_002_chars, List.length_replicate]
    decide +kernel
  · decide +kernel

theorem target_store_ok (m : word → Option byte) (a : word) (n : Nat)
    (Hlo : 0x1002000 ≤ bv_unsigned a) (Hhi : bv_unsigned a + (n : Int) ≤ 0x1005000) :
    store_ok target_segs m a n = true := by
  exact store_ok_window target_segs m 0x1002000 a 12288 n 0x1002000 0x1005000
    (by decide) (by decide) (by omega) target_data_wseg Hlo Hhi

/-- The 1024-byte read buffers are fully inside writable byte-defined
segments. -/
theorem source_rb_wseg :
    wseg_ok source_segs 0x13008 (word_to_nat (Z_to_bv 64 1024)) = true := by
  change wseg_ok source_segs 0x13008 1024 = true
  apply wseg_ok_backed source_segs SourceMemImage_segment_003 _ _
    [SourceMemImage_seg_bytes_003_chars]
  · simp only [wseg_cover, source_segs, Source.loaded_segments,
      SourceMemImage_loaded_segments,
      (show SourceMemImage_segment_000.seg_base = 0x10000 from rfl),
      (show SourceMemImage_segment_000.seg_size = 0x1000 from rfl),
      (show SourceMemImage_segment_001.seg_base = 0x11000 from rfl),
      (show SourceMemImage_segment_001.seg_size = 0x1000 from rfl),
      (show SourceMemImage_segment_002.seg_base = 0x12000 from rfl),
      (show SourceMemImage_segment_002.seg_size = 0x1000 from rfl),
      (show SourceMemImage_segment_003.seg_base = 0x13000 from rfl),
      (show SourceMemImage_segment_003.seg_size = 0x3000 from rfl),
      bv_unsigned, BitVec.reduceToNat, Int.cast_ofNat_Int, Int.reduceAdd,
      Int.reduceLT, Int.reduceLE, and_true, and_false, ite_true, ite_false]
  · decide +kernel
  · exact congrArg (fun x => [x]) tail1_src_seg3_chars_eq
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    exact SourceMemImage_seg_bytes_003_ascii
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    exact SourceMemImage_seg_bytes_003_hex
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    simp only [SourceMemImage_seg_bytes_003_chars, List.length_replicate]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      SourceMemImage_seg_bytes_003_chars, List.length_replicate]
    decide +kernel
  · decide +kernel

theorem target_rb_wseg :
    wseg_ok target_segs 0x10022ec (word_to_nat (Z_to_bv 64 1024)) = true := by
  change wseg_ok target_segs 0x10022ec 1024 = true
  apply wseg_ok_backed target_segs TargetMemImage_segment_002 _ _
    [TargetMemImage_seg_bytes_002_chars]
  · simp only [wseg_cover, target_segs, Target.loaded_segments,
      TargetMemImage_loaded_segments,
      (show TargetMemImage_segment_000.seg_base = 0x1000000 from rfl),
      (show TargetMemImage_segment_000.seg_size = 0x1000 from rfl),
      (show TargetMemImage_segment_001.seg_base = 0x1001000 from rfl),
      (show TargetMemImage_segment_001.seg_size = 0x1000 from rfl),
      (show TargetMemImage_segment_002.seg_base = 0x1002000 from rfl),
      (show TargetMemImage_segment_002.seg_size = 0x3000 from rfl),
      bv_unsigned, BitVec.reduceToNat, Int.cast_ofNat_Int, Int.reduceAdd,
      Int.reduceLT, Int.reduceLE, and_true, and_false, ite_true, ite_false]
  · decide +kernel
  · exact congrArg (fun x => [x]) tail1_tgt_seg2_chars_eq
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    exact TargetMemImage_seg_bytes_002_ascii
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    exact TargetMemImage_seg_bytes_002_hex
  · intro cs h
    simp only [List.mem_singleton] at h
    rw [h]
    simp only [TargetMemImage_seg_bytes_002_chars, List.length_replicate]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      TargetMemImage_seg_bytes_002_chars, List.length_replicate]
    decide +kernel
  · decide +kernel

/-- Reading a single byte through a disjoint `wbytes` one-byte store. -/
theorem rdn_wbytes1_out (segs : List Segment) (m : word → Option byte)
    (addr : word) (c : byte) (a : word) (n : Nat)
    (Hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64)
    (Hd : bv_unsigned addr < bv_unsigned a ∨
      bv_unsigned a + (n : Int) ≤ bv_unsigned addr) :
    rdn segs (wbytes m addr [c]) a n = rdn segs m a n := by
  apply rdn_ext segs n _ _ a Hnw
  intro x Hx
  rcases Hd with Hd | Hd
  · apply wbytes_above [c] m addr x
    simp only [List.length_singleton]
    omega
  · apply wbytes_below [c] m addr x
    · simp only [List.length_singleton]
      have hr := u64_range addr
      omega
    · omega

/-- Append a single byte to a buffer read-back: if `rdn mem base |L| = L`
then storing one byte at `base+|L|` extends the read-back to `L++[c]`. -/
theorem rdn_snoc_store (segs : List Segment) (mem : word → Option byte)
    (base : word) (L : List byte) (c : byte)
    (Hnw : bv_unsigned base + (L.length : Int) + 1 ≤ 2 ^ 64)
    (HL : rdn segs mem base L.length = some L) :
    rdn segs (wbytes mem (base + nat_to_word L.length) [c]) base (L.length + 1) =
      some (L ++ [c]) := by
  have Hu : bv_unsigned (base + nat_to_word L.length) =
      bv_unsigned base + (L.length : Int) := by
    rw [word_add_nat]
    apply u_Z2bv
    · have h := u64_range base
      omega
    · omega
  apply rdn_app segs _ L.length 1 base L [c]
  · rw [rdn_wbytes1_out segs mem _ c base L.length (by omega) (Or.inr (by omega))]
    exact HL
  · apply rdn_wbytes_hit
    simp only [List.length_singleton]
    omega

/-- `to_rd` at the raw ecall post-state record, at this example's chunk
count of 1024: a7=63 (read), a0=0 (stdin), a1=buffer, a2=1024, buffer
writable, plus the EOF (`to_out`) and per-block (`procs`)
continuations. -/
theorem trd_here_rec (St : Type) (segs : List Segment)
    (ff : St → byte → Option St) (oo : St → List byte) (e : word)
    (LH : St → machine_state → Prop) (a : St) (regs : bvmap 5 word)
    (pc : word) (mem rom : word → Option byte) (buf : word)
    (H17 : bv_unsigned (getr regs 17) = 63)
    (H10 : reg_get regs 10 = Z_to_bv 64 0)
    (H11 : reg_get regs 11 = buf)
    (H12 : reg_get regs 12 = Z_to_bv 64 1024)
    (Hw : wseg_ok segs buf (word_to_nat (Z_to_bv 64 1024)) = true)
    /- The range passes `access_ok`, which `vfs_read` tests before the
    input is consulted. `DrainSim.ReadPend` asks for this on top of
    the buffer being mapped, because `read_bytes_map`'s walk wraps at
    2^64 while `access_ok` reads `buf + 1024` exactly. Both buffers
    here are link-time constants. -/
    (Haok : access_okb buf (bv_unsigned (Z_to_bv 64 1024)) = true)
    (Hout : to_out segs (oo a)
      (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom))
    (Hobm : buf_modeled (oo a))
    (Hbytes : ∀ bs, 1 ≤ (bs.length : Int) → (bs.length : Int) ≤ 1024 →
      match procs ff a bs with
      | some a' => lh_next segs LH a'
          (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
            (write_to_mem mem buf bs) rom)
      | none => to_exit segs e
          (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
            (write_to_mem mem buf bs) rom)) :
    to_rd segs (Z_to_bv 64 1024) ff oo e LH a
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom } := by
  apply LinuxProcessSemantics.Common.DrainSim.to_rd.trd_here
  refine ⟨buf, getr regs 17, rfl, H17, H10, H11, H12, ?_, Haok, ?_, Hobm, ?_⟩
  · exact wseg_ok_wdef segs buf (Z_to_bv 64 1024) _ Hw
  · rw [adv_set]
    exact Hout
  · intro bs Hlo Hhi
    rw [adv_apply_write]
    exact Hbytes bs Hlo Hhi

/-- `to_out` emitting `bs` then exit 0, at the raw write ecall record: a7=64
(write), a0=1 (stdout), buffer bytes read back, exit-0 continuation. -/
theorem tout_wr_rec (segs : List Segment) (bs : List byte) (regs : bvmap 5 word)
    (pc : word) (mem rom : word → Option byte)
    (H17 : bv_unsigned (getr regs 17) = 64)
    (H10 : reg_get regs 10 = Z_to_bv 64 1)
    (Hr : ms_read_bytes
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some bs)
    (Hnb : 1 ≤ bs.length)
    (Hcont : ∀ n, 1 ≤ n → n ≤ bs.length →
      to_wall_tail segs (Z_to_bv 64 1)
        (mkst (regupd regs 10 (len_word (bs.take n))) (v_addi pc 4) mem rom)
        (bs.drop n) (to_exit segs (Z_to_bv 64 0))) :
    to_out segs bs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom } := by
  apply to_out.tout_wr
  refine ⟨Hnb, ?_⟩
  exact twl_write_rec segs (Z_to_bv 64 1) (to_exit segs (Z_to_bv 64 0))
    bs regs pc mem rom H17 H10 Hr Hnb Hcont

/-- Exit with code `code` at the raw ecall record: a7=93, a0=code. -/
theorem te_here_rec (segs : List Segment) (code : word) (regs : bvmap 5 word)
    (pc : word) (mem rom : word → Option byte)
    (H17 : bv_unsigned (getr regs 17) = 93) (H10 : reg_get regs 10 = code) :
    to_exit segs code
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom } := by
  exact to_exit.te_here _ (getr regs 17) rfl (Or.inl H17) H10

end LinuxProcessSemantics.Examples.tail1_ns.tail1_ns_defs
