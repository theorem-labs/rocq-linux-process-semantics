import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.CatSim

/-! # Common.CatExec — the store and read theory for the argv binaries

Ported from `theories/Common/CatExec.v` at
2cde689f94c086b868999970834b76a25616b94a: the part of it `cat1024_ns`'s
`Proof.v` reaches (`Print All Dependencies` of its
`strong_universal`, ticket E-proof-library), with the Rocq statements.

Rocq's file imports `ExitSim` and `CatSim` for its `to_wexit`
constructors; this module imports `CatSim`, which also imports `ExitSim`.
Sections appended at the end of
this file since, each headed by the ticket that added it, port some of it.

`length_Z_to_le_bytes` is `protected`, which changes how it is named, in
this namespace as well as outside it, and not its statement (its docstring
says why).

Universes.  In `theories/Common/CatExec.v`, the plain `Type` binders of
`flat_map_app'`, `skipn_nth` and `flat_map_split` introduce a global universe
per binder: `flat_map_app'` has `A : Type@{flat_map_app'.u0}` and
`B : Type@{flat_map_app'.u1}`, `skipn_nth` has `A : Type@{skipn_nth.u0}`,
and `flat_map_split` has `A : Type@{flat_map_split.u0}` and
`B : Type@{flat_map_split.u1}`.  Instantiating a binder with a type in
`Type@{v}` constrains `v` to be at most that binder's global universe.
Here the binder universes are independent parameters of the theorem, with no upper bound,
as pinned by `flat_map_app'_any_universe`, `skipn_nth_any_universe` and
`flat_map_split_any_universe`.  Rocq's binders also accept propositions by
cumulativity; Lean's `List` takes a `Type u` element type.  The `#guard_msgs`
pins after those theorems record the refusal of `True` for each lemma. -/

namespace LinuxProcessSemantics.Common.CatExec

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec

/-! ## (A) `ms_read_bytes` → `rdn` bridge -/

theorem ms_read_bytes_aux_rdn (segs : List Segment) (ms : machine_state) (n : Nat) (addr : word)
    (hrom : ms.ms_rom = seg_rom segs) :
    ms_read_bytes_aux ms addr n = rdn segs ms.ms_mem addr n := by
  induction n generalizing addr with
  | zero => rfl
  | succ n ih =>
    -- the two sides are the same term under two copies of the match
    simp only [ms_read_bytes_aux, rdn, ms_read_byte, hrom, ih]
    rfl

theorem ms_read_bytes_rdn (segs : List Segment) (ms : machine_state) (addr len : word)
    (hrom : ms.ms_rom = seg_rom segs) :
    ms_read_bytes ms addr len = rdn segs ms.ms_mem addr (word_to_nat len) :=
  ms_read_bytes_aux_rdn segs ms _ addr hrom

/-! ## (B) Store-double memory theory -/

/-- Memory-level mirror of the interpreter's store path (`write_to_mem`). -/
def wbytes (m : word → Option byte) (addr : word) (bs : List byte) : word → Option byte :=
  match bs with
  | [] => m
  | b :: rest => wbytes (fun a => if bv_eqb a addr then some b else m a) (addr + 1) rest

/-- Reads at/above the end of the written range are unchanged.  The bound
`addr + length bs ≤ x < 2^64` already rules out a wrapping write walk, so no
extra no-overflow hypothesis is needed. -/
theorem wbytes_above (bs : List byte) (m : word → Option byte) (addr x : word)
    (hle : bv_unsigned addr + (bs.length : Int) ≤ bv_unsigned x) :
    wbytes m addr bs x = m x := by
  induction bs generalizing m addr with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons] at hle
    have hx := u64_range x
    have hu1 : bv_unsigned (addr + 1) = bv_unsigned addr + 1 := u_add1 addr (by omega)
    simp only [wbytes]
    rw [ih _ _ (by omega)]
    have hne : x ≠ addr := by
      intro h
      rw [h] at hle
      omega
    simp only [bv_eqb_neq x addr hne, Bool.false_eq_true, ↓reduceIte]

theorem rdn_wbytes_disjoint (segs : List Segment) (bs : List byte) (m : word → Option byte)
    (addr a : word) (n : Nat)
    (hle : bv_unsigned addr + (bs.length : Int) ≤ bv_unsigned a)
    (hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn segs (wbytes m addr bs) a n = rdn segs m a n := by
  apply rdn_ext segs n _ _ a hnw
  intro x hx
  exact wbytes_above bs m addr x (by omega)

/-- Reads below the written range are unchanged.  The no-overflow
hypothesis `addr + length bs ≤ 2^64` is Rocq's: the write walk is a
wrapping add, so without it the tail of a huge write could wrap to `x`. -/
theorem wbytes_below (bs : List byte) (m : word → Option byte) (addr x : word)
    (hnw : bv_unsigned addr + (bs.length : Int) ≤ 2 ^ 64)
    (hlt : bv_unsigned x < bv_unsigned addr) :
    wbytes m addr bs x = m x := by
  induction bs generalizing m addr with
  | nil => rfl
  | cons b rest ih =>
    have hne : x ≠ addr := by
      intro h
      rw [h] at hlt
      omega
    cases rest with
    | nil =>
      simp only [wbytes, bv_eqb_neq x addr hne, Bool.false_eq_true, ↓reduceIte]
    | cons b' rest' =>
      simp only [List.length_cons] at hnw
      have hu1 : bv_unsigned (addr + 1) = bv_unsigned addr + 1 := u_add1 addr (by omega)
      simp only [wbytes] at ih ⊢
      rw [ih _ _ (by simp only [List.length_cons]; omega) (by omega)]
      simp only [bv_eqb_neq x addr hne, Bool.false_eq_true, ↓reduceIte]

theorem rdn_wbytes_below (segs : List Segment) (bs : List byte) (m : word → Option byte)
    (addr a : word) (n : Nat)
    (hle : bv_unsigned a + (n : Int) ≤ bv_unsigned addr)
    (hnw : bv_unsigned addr + (bs.length : Int) ≤ 2 ^ 64) :
    rdn segs (wbytes m addr bs) a n = rdn segs m a n := by
  have ha := u64_range addr
  apply rdn_ext segs n _ _ a (by omega)
  intro x hx
  exact wbytes_below bs m addr x hnw (by omega)

/-- `protected`: `BvBase.length_Z_to_le_bytes` has the same name and
statement, and a file opening both namespaces would otherwise read the bare
name as ambiguous (Rocq settles the clash silently by import order). -/
protected theorem length_Z_to_le_bytes (n : Nat) (z : Int) : (Z_to_le_bytes n z).length = n :=
  BvBase.length_Z_to_le_bytes n z

theorem length_N_to_le_bytes (n : Nat) (v : word) : (word_to_le_bytes n v).length = n :=
  CatExec.length_Z_to_le_bytes n (bv_unsigned v)

/-- The tree interpreter's byte-writer `write_to_mem` IS `wbytes` (same
recursion, byte `i` at `addr + i`). -/
theorem write_to_mem_wbytes (bs : List byte) (m : word → Option byte) (addr : word) :
    write_to_mem m addr bs = wbytes m addr bs := by
  induction bs generalizing m addr with
  | nil => rfl
  | cons b rest ih => exact ih _ _

/-! ## (C) argv bounds -/

theorem valid_argv_len (av : List (List byte)) (h : valid_argv av) :
    (av.length : Int) ≤ 1024 :=
  h.1.2

/-! ## (D) Post-svc register collapse -/

/-- Collapse `advance_past_svc (set_gpr0 <record> v)` to a `mkst`: advance
the PC past the svc after writing the syscall return to x10. -/
theorem adv_set (regs : bvmap 5 word) (pc : word) (sv : Option word)
    (mem rom : word → Option byte) (v : word) :
    advance_past_svc (set_gpr0
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc, ms_svc_pending := sv,
        ms_resv := none, ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom } v)
    = mkst (regupd regs 10 v) (v_addi pc 4) mem rom := by
  have h10 : bv_eqb (10 : reg) 0 = false := bv_eqb_neq _ _ (by decide)
  have hf : Z_to_bv 32 0 = (0 : BitVec 32) := by decide
  simp only [advance_past_svc, set_gpr0, set_reg, h10, Bool.false_eq_true, ↓reduceIte,
    ms_pc, mkst, regupd, hf, b_npc4]

/-! ## Additions for ticket E-proof-library-2c: the argv stack-layout group

Ported from the same Rocq file at the baseline the header names, with the
Rocq statements, for `Common/SeqExec.lean`'s `argv_ptr_bounds`,
`Common/MuslStrlen.lean` and `Common/ArgvEnv.lean`.  The section letters
here are the Rocq file's, not this file's: the list helpers of Rocq's (C)
(this section does not port its three number facts, `natN_le`,
`of_nat_131071` and `of_nat_2097152`), the stack-layout abbreviations of
Rocq's (D) with `nth_string_addrs` and `cat_argv_ptr_offset`, the
`build_stack_bytes` decompositions of Rocq's (E) that those files reach
(this section does not port `read_argv_byte_k` or `read_argv_str_k`), and
from Rocq's (E.5) `byte_at` and
`valid_argv_str_len`.  Rocq's `nth k l d` is `l.getD k d`, `firstn`/`skipn`
are `take`/`drop`, `flat_map f l` is `l.flatMap f`, `Z.of_nat` is the
`Nat`-to-`Int` cast, and Rocq's `++`, which associates to the right, is
written with the parentheses Lean's left-associative `++` needs to state
the same term. -/

open LinuxProcessSemantics.LinuxProcessSem.StackLayout

universe u v in
theorem flat_map_app' {A : Type u} {B : Type v} (f : A → List B) (l1 l2 : List A) :
    (l1 ++ l2).flatMap f = l1.flatMap f ++ l2.flatMap f :=
  List.flatMap_append

universe u v in
theorem flat_map_app'_any_universe : ∀ {A : Type u} {B : Type v}
    (f : A → List B) (l1 l2 : List A),
    (l1 ++ l2).flatMap f = l1.flatMap f ++ l2.flatMap f :=
  flat_map_app'

universe u in
theorem skipn_nth {A : Type u} (l : List A) (k : Nat) (d : A) (hk : k < l.length) :
    l.drop k = l.getD k d :: l.drop (k + 1) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.drop_eq_getElem_cons hk

universe u in
theorem skipn_nth_any_universe : ∀ {A : Type u}
    (l : List A) (k : Nat) (d : A) (_hk : k < l.length),
    l.drop k = l.getD k d :: l.drop (k + 1) :=
  skipn_nth

universe u v in
theorem flat_map_split {A : Type u} {B : Type v} (f : A → List B) (l : List A) (k : Nat) (d : A)
    (hk : k < l.length) :
    l.flatMap f = (l.take k).flatMap f ++ (f (l.getD k d) ++ (l.drop (k + 1)).flatMap f) := by
  conv => lhs; rw [← List.take_append_drop k l]
  rw [flat_map_app', skipn_nth l k d hk, List.flatMap_cons]

universe u v in
theorem flat_map_split_any_universe : ∀ {A : Type u} {B : Type v}
    (f : A → List B) (l : List A) (k : Nat) (d : A) (_hk : k < l.length),
    l.flatMap f = (l.take k).flatMap f ++ (f (l.getD k d) ++ (l.drop (k + 1)).flatMap f) :=
  flat_map_split

/-- error: Application type mismatch: The argument
  True
has type
  Prop
of sort `Type` but is expected to have type
  Type _
of sort `Type (_ + 1)` in the application
  @flat_map_app' True -/
#guard_msgs in
set_option pp.mvars false in
example := @flat_map_app' True

/-- error: Application type mismatch: The argument
  True
has type
  Prop
of sort `Type` but is expected to have type
  Type _
of sort `Type (_ + 1)` in the application
  @skipn_nth True -/
#guard_msgs in
set_option pp.mvars false in
example := @skipn_nth True

/-- error: Application type mismatch: The argument
  True
has type
  Prop
of sort `Type` but is expected to have type
  Type _
of sort `Type (_ + 1)` in the application
  @flat_map_split True -/
#guard_msgs in
set_option pp.mvars false in
example := @flat_map_split True

theorem flat_map_le8_decomp (l : List word) (k : Nat) (hk : k < l.length) :
    l.flatMap word_le8 =
      (l.take k).flatMap word_le8 ++
        (word_le8 (l.getD k (Z_to_bv 64 0)) ++ (l.drop (k + 1)).flatMap word_le8) :=
  flat_map_split word_le8 l k (Z_to_bv 64 0) hk

theorem flatten_strings_decomp (strs : List (List byte)) (k : Nat) (hk : k < strs.length) :
    flatten_strings strs =
      flatten_strings (strs.take k) ++
        ((strs.getD k [] ++ [Z_to_bv 8 0]) ++ flatten_strings (strs.drop (k + 1))) :=
  flat_map_split (fun s => s ++ [Z_to_bv 8 0]) strs k [] hk

theorem total_arg_bytes_cons (s : List byte) (l : List (List byte)) :
    total_arg_bytes_nat (s :: l) = s.length + 1 + total_arg_bytes_nat l := rfl

theorem total_arg_bytes_firstn_le (k : Nat) (l : List (List byte)) :
    total_arg_bytes_nat (l.take k) ≤ total_arg_bytes_nat l := by
  induction k generalizing l with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    cases l with
    | nil => exact Nat.le_refl _
    | cons s rest =>
      rw [List.take_succ_cons, total_arg_bytes_cons, total_arg_bytes_cons]
      have := ih rest
      omega

def cat_struct_size (av ev : List (List byte)) : Nat :=
  8 + (av.length + 1) * 8 + (ev.length + 1) * 8 + auxv_size

def cat_string_base (sp : word) (av ev : List (List byte)) : word :=
  sp + nat_to_word (cat_struct_size av ev)

def cat_env_base (sp : word) (av ev : List (List byte)) : word :=
  cat_string_base sp av ev + nat_to_word (total_arg_bytes_nat av)

/-- The k-th argv pointer value: the address of argv string k's bytes. -/
def cat_argv_ptr (sp : word) (av ev : List (List byte)) (k : Nat) : word :=
  (string_addrs (cat_string_base sp av ev) av).1.getD k (Z_to_bv 64 0)

theorem nth_string_addrs (strs : List (List byte)) (base : word) (k : Nat)
    (hk : k < strs.length) :
    (string_addrs base strs).1.getD k (Z_to_bv 64 0) =
      base + nat_to_word (total_arg_bytes_nat (strs.take k)) := by
  induction strs generalizing base k with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | cons s rest ih =>
    rw [string_addrs_fst_structure]
    cases k with
    | zero => exact (word_add_0 base).symm
    | succ k' =>
      rw [List.getD_cons_succ,
        ih (base + len_word s + 1) k' (by simp only [List.length_cons] at hk; omega),
        List.take_succ_cons, total_arg_bytes_cons, len_word_nat, word1_nat,
        nat_to_word_add_merge, nat_to_word_add_merge, Nat.add_assoc]

theorem cat_argv_ptr_offset (sp : word) (av ev : List (List byte)) (k : Nat)
    (hk : k < av.length) :
    cat_argv_ptr sp av ev k =
      cat_string_base sp av ev + nat_to_word (total_arg_bytes_nat (av.take k)) :=
  nth_string_addrs av (cat_string_base sp av ev) k hk

/-- The fixed-size struct prefix that precedes the string data. -/
def cat_struct_prefix (ph : PhdrInfo) (sp : word) (av ev : List (List byte))
    (uid hw : word) : List byte :=
  word_le8 (len_word av)
  ++ ((string_addrs (cat_string_base sp av ev) av).1.flatMap word_le8
  ++ (word_le8 (Z_to_bv 64 0)
  ++ ((string_addrs (cat_env_base sp av ev) ev).1.flatMap word_le8
  ++ (word_le8 (Z_to_bv 64 0) ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw))))

theorem length_cat_struct_prefix (ph : PhdrInfo) (sp : word) (av ev : List (List byte))
    (uid hw : word) :
    (cat_struct_prefix ph sp av ev uid hw).length = cat_struct_size av ev := by
  unfold cat_struct_prefix cat_struct_size
  simp only [List.length_append, length_flat_map_le8, length_string_addrs_fst,
    length_n_to_le_8, length_auxv_bytes]
  omega

/-- build = argc ++ argv_ptrs ++ <tail>. -/
theorem bsb_argv_prefix (ph : PhdrInfo) (sp : word) (av ev : List (List byte))
    (uid hw : word) (rnd : EntryDraw) :
    ∃ tail, build_stack_bytes ph sp av ev uid hw rnd =
      word_le8 (len_word av)
      ++ ((string_addrs (cat_string_base sp av ev) av).1.flatMap word_le8 ++ tail) := by
  unfold build_stack_bytes
  dsimp only
  rw [string_addrs_pair av]
  dsimp only
  rw [string_addrs_pair ev]
  dsimp only
  rw [length_auxv_bytes]
  exact ⟨_, by simp only [List.append_assoc]; rfl⟩

/-- build = (argc ++ argv_ptrs[<k]) ++ argv_ptrs[k] ++ <post>. -/
theorem bsb_ptr_k (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (k : Nat)
    (uid hw : word) (rnd : EntryDraw) (hk : k < av.length) :
    ∃ post, build_stack_bytes ph sp av ev uid hw rnd =
      (word_le8 (len_word av)
        ++ ((string_addrs (cat_string_base sp av ev) av).1.take k).flatMap word_le8)
      ++ (word_le8 ((string_addrs (cat_string_base sp av ev) av).1.getD k (Z_to_bv 64 0))
        ++ post) := by
  obtain ⟨tail, e⟩ := bsb_argv_prefix ph sp av ev uid hw rnd
  have hk' : k < (string_addrs (cat_string_base sp av ev) av).1.length := by
    rw [length_string_addrs_fst]
    exact hk
  rw [flat_map_le8_decomp _ k hk'] at e
  refine ⟨((string_addrs (cat_string_base sp av ev) av).1.drop (k + 1)).flatMap word_le8 ++ tail,
    ?_⟩
  rw [e]
  simp only [List.append_assoc]

theorem read_argv_ptr_k (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (av ev : List (List byte)) (k : Nat) (uid hw : word) (rnd : EntryDraw)
    (hk : k < av.length)
    (hnw : bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
        (sp + nat_to_word (8 + 8 * k)) 8 =
      some (word_le8 (cat_argv_ptr sp av ev k)) := by
  obtain ⟨post, e⟩ := bsb_ptr_k ph sp av ev k uid hw rnd hk
  have h' := read_at_offset_image segs ph sp av ev uid hw rnd _ _ post 8 e
    (length_n_to_le_8 _) hnw
  have hlen : (word_le8 (len_word av)
      ++ ((string_addrs (cat_string_base sp av ev) av).1.take k).flatMap word_le8).length =
      8 + 8 * k := by
    rw [List.length_append, length_n_to_le_8, length_flat_map_le8, List.length_take,
      length_string_addrs_fst]
    omega
  rw [hlen] at h'
  exact h'

/-- build = <struct prefix> ++ (<the argv strings, each with its NUL> ++
<tail>).  (Rocq's comment on this lemma describes `bsb_byte_k`, below.) -/
theorem bsb_strings_split (ph : PhdrInfo) (sp : word) (av ev : List (List byte))
    (uid hw : word) (rnd : EntryDraw) :
    ∃ tail, build_stack_bytes ph sp av ev uid hw rnd =
      cat_struct_prefix ph sp av ev uid hw ++ (flatten_strings av ++ tail) := by
  unfold build_stack_bytes cat_struct_prefix cat_env_base cat_string_base
  dsimp only
  rw [string_addrs_pair av]
  dsimp only
  rw [string_addrs_pair ev]
  dsimp only
  rw [length_auxv_bytes]
  exact ⟨_, by simp only [List.append_assoc]; rfl⟩

/-- build = <pre> ++ (argv[k] ++ [0]) ++ <post>, with `length pre` known. -/
theorem bsb_byte_k (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (k : Nat)
    (uid hw : word) (rnd : EntryDraw) (hk : k < av.length) :
    ∃ pre post, build_stack_bytes ph sp av ev uid hw rnd =
        pre ++ ((av.getD k [] ++ [Z_to_bv 8 0]) ++ post) ∧
      pre.length = cat_struct_size av ev + total_arg_bytes_nat (av.take k) := by
  obtain ⟨tail, e⟩ := bsb_strings_split ph sp av ev uid hw rnd
  rw [flatten_strings_decomp av k hk] at e
  refine ⟨cat_struct_prefix ph sp av ev uid hw ++ flatten_strings (av.take k),
    flatten_strings (av.drop (k + 1)) ++ tail, ?_, ?_⟩
  · rw [e]
    simp only [List.append_assoc]
  · rw [List.length_append, length_cat_struct_prefix, length_flatten_strings]

/-- `byte_at s k` is the NUL-padded k-th byte of `s` (the byte an argv
string reads back as at offset `k`, including the implicit terminating NUL
at `k = length s`). -/
def byte_at (s : List byte) (k : Nat) : byte :=
  (s ++ [Z_to_bv 8 0]).getD k (Z_to_bv 8 0)

theorem valid_argv_str_len (av : List (List byte)) (k : Nat) (h : valid_argv av)
    (hk : k < av.length) :
    ((av.getD k []).length : Int) ≤ 131071 := by
  have hmem : av.getD k [] ∈ av := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact List.getElem_mem hk
  exact h.2.2.1 _ hmem

/-! ## T157: remaining store and stack-window facts -/

open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.Riscv.DecodeC

theorem rdn_wbytes_out (segs : List Segment) (bs : List byte) (m : word → Option byte)
    (addr a : word) (n : Nat)
    (hout : bv_unsigned a + (n : Int) ≤ bv_unsigned addr ∨
      bv_unsigned addr + (bs.length : Int) ≤ bv_unsigned a)
    (hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64)
    (hnw' : bv_unsigned addr + (bs.length : Int) ≤ 2 ^ 64) :
    rdn segs (wbytes m addr bs) a n = rdn segs m a n := by
  rcases hout with hb | hd
  · exact rdn_wbytes_below segs bs m addr a n hb hnw'
  · exact rdn_wbytes_disjoint segs bs m addr a n hd hnw

theorem step_sd (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (hfetch : fetch_word segs pc = some w) (hecall : is_ecall w = false)
    (hdecode : decode_any w = some (.Store .SZ8 rs1 rs2 imm, 4))
    (hok : store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) 8 = true) :
    ∃ bs, bs.length = 8 ∧
      RiscvSemantics.step segs (mkst regs pc mem rom) =
        MachineOk (mkst regs (v_addi pc 4)
          (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) bs) rom) := by
  refine ⟨word_to_le_bytes 8 (getr regs rs2), rfl, ?_⟩
  step_pipeline hfetch hecall hdecode
  simp only [exec, store_val, rget_mk, b_addsext, interp_eff, interp_eff_accesses,
    width_bytes, hok, ↓reduceIte]
  rw [← word_to_le_bytes, write_to_mem_wbytes, npc4]
  rfl

theorem stack_max_size_val : stack_max_size = 8388608 := by decide +kernel

theorem wrap_mem_below (ph : PhdrInfo) (sp : word) (argv envp : List (List byte))
    (addr uid hw : word) (rnd : EntryDraw)
    (hlt : bv_unsigned addr < bv_unsigned sp - stack_max_size) :
    wrap_mem ph sp argv envp uid hw rnd addr = none := by
  have hs := stack_max_size_val
  have hbelow : ¬ bv_unsigned sp ≤ bv_unsigned addr := by omega
  have hgate : ¬ bv_unsigned sp - stack_max_size ≤ bv_unsigned addr := by omega
  simp [wrap_mem, stack_to_mem, hbelow, hgate]

/-! ## T157: number conversions -/

theorem natN_le (n m : Nat) (h : n ≤ m) : n ≤ m := h

theorem of_nat_131071 : ((131071 : Nat) : Int) = 131071 := by decide +kernel

theorem of_nat_2097152 : ((2097152 : Nat) : Int) = 2097152 := by decide +kernel

/-! ## T157: argv byte and string reads -/

theorem read_argv_byte_k (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (av ev : List (List byte)) (k j : Nat) (uid hw : word) (rnd : EntryDraw)
    (hk : k < av.length) (hj : j ≤ (av.getD k []).length)
    (hnw : bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
        (cat_argv_ptr sp av ev k + nat_to_word j) 1 =
      some [(av.getD k [] ++ [Z_to_bv 8 0]).getD j (Z_to_bv 8 0)] := by
  obtain ⟨pre, post, e, hlen⟩ := bsb_byte_k ph sp av ev k uid hw rnd hk
  let s := av.getD k [] ++ [Z_to_bv 8 0]
  have hj' : j < s.length := by
    simp only [s, List.length_append, List.length_cons, List.length_nil]
    omega
  have he : build_stack_bytes ph sp av ev uid hw rnd =
      (pre ++ s.take j) ++ ([s.getD j (Z_to_bv 8 0)] ++ (s.drop (j + 1) ++ post)) := by
    rw [e]
    change pre ++ (s ++ post) = _
    conv => lhs; arg 2; arg 1; rw [← List.take_append_drop j s,
      skipn_nth s j (Z_to_bv 8 0) hj']
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have h := read_at_offset_image segs ph sp av ev uid hw rnd _ _ _ 1 he rfl hnw
  have hl : (pre ++ s.take j).length =
      cat_struct_size av ev + total_arg_bytes_nat (av.take k) + j := by
    rw [List.length_append, List.length_take, hlen, Nat.min_eq_left (Nat.le_of_lt hj')]
  rw [hl] at h
  rw [cat_argv_ptr_offset sp av ev k hk, cat_string_base,
    nat_to_word_add_merge, nat_to_word_add_merge]
  simpa only [Nat.add_assoc] using h

theorem read_argv_str_k (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (av ev : List (List byte)) (k : Nat) (uid hw : word) (rnd : EntryDraw)
    (hk : k < av.length)
    (hnw : bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
        (cat_argv_ptr sp av ev k) (av.getD k []).length = some (av.getD k []) := by
  obtain ⟨pre, post, e, hlen⟩ := bsb_byte_k ph sp av ev k uid hw rnd hk
  have he : build_stack_bytes ph sp av ev uid hw rnd =
      pre ++ (av.getD k [] ++ ([Z_to_bv 8 0] ++ post)) := by
    rw [e, List.append_assoc]
  have h := read_at_offset_image segs ph sp av ev uid hw rnd pre _ _ _ he rfl hnw
  rw [hlen] at h
  rw [cat_argv_ptr_offset sp av ev k hk, cat_string_base, nat_to_word_add_merge]
  exact h

/-! ## T157: byte projections and argv validity -/

theorem nth_lt_byte_at (s : List byte) (j : Nat) (hj : j < s.length) :
    byte_at s j = s.getD j (Z_to_bv 8 0) := by
  simp only [byte_at, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem byte_at_len (s : List byte) : byte_at s s.length = Z_to_bv 8 0 := by
  simp only [byte_at, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_refl s.length), Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]

theorem byte_at_nz (s : List byte) (j : Nat) (hnz : ¬ Z_to_bv 8 0 ∈ s)
    (hj : j < s.length) : byte_at s j ≠ Z_to_bv 8 0 := by
  rw [nth_lt_byte_at s j hj, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj, Option.getD_some]
  intro he
  exact hnz (he ▸ List.getElem_mem hj)

theorem byte_at_bound (s : List byte) (j : Nat) : bv_unsigned (byte_at s j) < 256 :=
  (u8_range _).2

theorem valid_argv_nonempty (av : List (List byte)) (h : valid_argv av) :
    1 ≤ av.length := by
  have := h.1.1
  omega

theorem valid_argv_str_nz (av : List (List byte)) (k : Nat) (h : valid_argv av)
    (hk : k < av.length) : ¬ Z_to_bv 8 0 ∈ av.getD k [] := by
  apply h.2.2.2.1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

theorem valid_argv_str_plain (av : List (List byte)) (k : Nat) (h : valid_argv av)
    (hk : k + 1 < av.length) (hdot : path_eqb (av.getD (k + 1) []) dot_path = false) :
    openat_plain_name (av.getD (k + 1) []) = true := by
  have hnth : av.getD (k + 1) [] = av.tail.getD k [] := by
    cases av with
    | nil => rfl
    | cons a av => rfl
  have hk' : k < av.tail.length := by simp only [List.length_tail]; omega
  have hmem : av.tail.getD k [] ∈ av.tail := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
    exact List.getElem_mem hk'
  obtain ⟨hsl, hdd⟩ := h.2.2.2.2 _ hmem
  rw [hnth] at hdot ⊢
  simp only [openat_plain_name, path_is_dirref, hdot, hsl, hdd]
  rfl

theorem valid_argv_str_bytes (av : List (List byte)) (k : Nat) (_h : valid_argv av)
    (_hk : k < av.length) : ∀ b ∈ av.getD k [], bv_unsigned b < 256 := by
  intro b _
  exact (u8_range b).2

/-! ## T157: predecessor and exit-after-writes constructors -/

theorem v_addi_pred (x : word) : v_addi (x + 1) (-1) = x := by
  apply bv_eq_of_unsigned
  rw [v_addi, Z_to_bv_unsigned, bv_unsigned_add]
  change ((bv_unsigned x + 1) % 2 ^ 64 + -1) % 2 ^ 64 = bv_unsigned x
  rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]
  have hx := u64_range x
  rw [show bv_unsigned x + 1 + -1 = bv_unsigned x by omega,
    Int.emod_eq_of_lt hx.1 hx.2]

def pend (regs : bvmap 5 word) (pc : word) (mem rom : word → Option byte) : machine_state :=
  { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
    ms_svc_pending := some (Z_to_bv 64 64), ms_resv := none,
    ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }

open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim

theorem tw_write_gen (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (buf : List byte) (bufs : List (List byte)) (code : word)
    (hg0 : ms_gpr (pend regs pc mem rom) 0 = Z_to_bv 64 1)
    (hr : ms_read_bytes (pend regs pc mem rom)
      (ms_gpr (pend regs pc mem rom) 1) (ms_gpr (pend regs pc mem rom) 2) = some buf)
    (hnb : 1 ≤ buf.length)
    (hcont : ∀ n, 1 ≤ n → n ≤ buf.length →
      to_wexit segs (mkst (regupd regs 10 (len_word (buf.take n)))
        (v_addi pc 4) mem rom) bufs code) :
    to_wexit segs (pend regs pc mem rom) (buf :: bufs) code := by
  refine to_wexit.tw_write _ _ _ _ _ rfl rfl hg0 hr hnb ?_
  intro n hn1 hn2
  unfold pend
  rw [adv_set]
  exact hcont n hn1 hn2

theorem tw_exit0 (segs : List Segment) (ms : machine_state) (x8 : word)
    (hsvc : ms.ms_svc_pending = some x8) (hex : is_exit_no x8)
    (hg0 : ms_gpr ms 0 = Z_to_bv 64 0) :
    to_wexit segs ms [] (Z_to_bv 64 0) := by
  have hc : bv_and (ms_gpr ms 0) (Z_to_bv 64 255) = Z_to_bv 64 0 := by
    rw [hg0]
    rfl
  rw [← hc]
  exact to_wexit.tw_exit ms x8 hsvc hex

theorem tw_write_rec (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (buf : List byte) (bufs : List (List byte)) (code : word)
    (h17 : bv_unsigned (getr regs 17) = 64) (h10 : reg_get regs 10 = Z_to_bv 64 1)
    (hr : ms_read_bytes
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
        ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some buf)
    (hnb : 1 ≤ buf.length)
    (hcont : ∀ n, 1 ≤ n → n ≤ buf.length →
      to_wexit segs (mkst (regupd regs 10 (len_word (buf.take n)))
        (v_addi pc 4) mem rom) bufs code) :
    to_wexit segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
        ms_mem := mem, ms_rom := rom } (buf :: bufs) code := by
  refine to_wexit.tw_write _ _ _ _ _ rfl h17 h10 hr hnb ?_
  intro n hn1 hn2
  rw [adv_set]
  exact hcont n hn1 hn2

theorem tw_exit_rec (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte)
    (h17 : bv_unsigned (getr regs 17) = 93) (h10 : reg_get regs 10 = Z_to_bv 64 0) :
    to_wexit segs
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
        ms_mem := mem, ms_rom := rom } [] (Z_to_bv 64 0) :=
  tw_exit0 segs _ _ rfl (Or.inl h17) h10

end LinuxProcessSemantics.Common.CatExec
