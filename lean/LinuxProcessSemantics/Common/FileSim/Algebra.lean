import LinuxProcessSemantics.Common.CatExec

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # Common.FileSim — algebra and string read-back

Sections C–G of `theories/Common/FileSim.v`, with the Rocq names,
statements and argument order. Rocq `firstn`/`skipn` are `List.take`/`List.drop`,
`nth k av []` is `av.getD k []`, and `In` is list membership.
The polymorphic list lemmas use Lean's `Type u`.
-/

namespace LinuxProcessSemantics.Common.FileSim

universe u

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec

/-! ## Filesystem algebra -/

theorem path_eqb_neq (p q : path) (hne : p ≠ q) : path_eqb p q = false := by
  cases h : path_eqb p q with
  | false => rfl
  | true => exact False.elim (hne ((path_eqb_eq p q).1 h))

theorem fs_lookup_set_eq (fs : Fs) (p : path) (d : List byte) :
    fs_lookup (fs_set fs p d) p = some d := by
  induction fs with
  | nil => simp only [fs_set, fs_lookup, path_eqb_refl, ite_true]
  | cons ent fs ih =>
    rcases ent with ⟨q, dq⟩
    cases hl : path_ltb p q <;> cases he : path_eqb p q <;>
      simp only [fs_set, hl, he, fs_lookup, path_eqb_refl, ite_true, Bool.false_eq_true,
        ite_false, ih]

theorem fs_lookup_set_neq (fs : Fs) (p : path) (d : List byte) (q : path)
    (hne : q ≠ p) : fs_lookup (fs_set fs p d) q = fs_lookup fs q := by
  induction fs with
  | nil => simp only [fs_set, fs_lookup, path_eqb_neq q p hne, Bool.false_eq_true, ite_false]
  | cons ent fs ih =>
    rcases ent with ⟨r, dr⟩
    cases hl : path_ltb p r with
    | true => simp only [fs_set, hl, ite_true, fs_lookup, path_eqb_neq q p hne,
        Bool.false_eq_true, ite_false]
    | false =>
      cases he : path_eqb p r with
      | true =>
        have hr := (path_eqb_eq p r).1 he
        subst r
        simp only [fs_set, hl, he, Bool.false_eq_true, ite_false, ite_true, fs_lookup,
          path_eqb_neq q p hne]
      | false =>
        simp only [fs_set, hl, he, Bool.false_eq_true, ite_false, fs_lookup, ih]

theorem path_ltb_irrefl (p : path) : path_ltb p p = false := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [path_ltb, bv_ltu, BitVec.ult, Nat.lt_irrefl, decide_false,
      PropExec.bv_eqb_refl, ih, Bool.true_and, Bool.false_or]

theorem fs_set_set (fs : Fs) (p : path) (d d' : List byte) :
    fs_set (fs_set fs p d) p d' = fs_set fs p d' := by
  induction fs with
  | nil => simp only [fs_set, path_ltb_irrefl, path_eqb_refl, Bool.false_eq_true,
      ite_false, ite_true]
  | cons ent fs ih =>
    rcases ent with ⟨q, dq⟩
    cases hl : path_ltb p q <;> cases he : path_eqb p q <;>
      simp only [fs_set, hl, he, path_ltb_irrefl, path_eqb_refl, Bool.false_eq_true,
        ite_false, ite_true, ih]

/-! ## Descriptor table algebra -/

theorem fd_lookup_cons_eq (fds : List (word × FdEntry)) (fd : word) (e : FdEntry) :
    fd_lookup ((fd, e) :: fds) fd = some e := by
  simp only [fd_lookup, PropExec.bv_eqb_refl, ite_true]

theorem fd_lookup_cons_neq (fds : List (word × FdEntry)) (k : word) (e : FdEntry)
    (fd : word) (hne : k ≠ fd) : fd_lookup ((k, e) :: fds) fd = fd_lookup fds fd := by
  simp only [fd_lookup, bv_eqb_neq k fd hne, Bool.false_eq_true, ite_false]

theorem fd_lookup_cons_None (fds : List (word × FdEntry)) (k : word) (e : FdEntry)
    (fd : word) (h : fd_lookup ((k, e) :: fds) fd = none) :
    k ≠ fd ∧ fd_lookup fds fd = none := by
  have hne : k ≠ fd := by
    intro he
    subst k
    rw [fd_lookup_cons_eq] at h
    cases h
  exact ⟨hne, (fd_lookup_cons_neq fds k e fd hne).symm.trans h⟩

theorem fd_filter_id (fds : List (word × FdEntry)) (fd : word)
    (h : fd_lookup fds fd = none) :
    fds.filter (fun p => !(bv_eqb p.1 fd)) = fds := by
  induction fds with
  | nil => rfl
  | cons ent fds ih =>
    rcases ent with ⟨k, e⟩
    obtain ⟨hne, ht⟩ := fd_lookup_cons_None fds k e fd h
    simp only [List.filter_cons, bv_eqb_neq k fd hne, Bool.not_false, ite_true, ih ht]

theorem fd_insert_fresh (fds : List (word × FdEntry)) (fd : word) (e : FdEntry)
    (h : fd_lookup fds fd = none) : fd_insert fds fd e = (fd, e) :: fds := by
  rw [fd_insert, fd_filter_id fds fd h]

theorem fd_lookup_filter_neq (fds : List (word × FdEntry)) (fd fd' : word)
    (hne : fd' ≠ fd) :
    fd_lookup (fds.filter (fun p => !(bv_eqb p.1 fd))) fd' = fd_lookup fds fd' := by
  induction fds with
  | nil => rfl
  | cons ent fds ih =>
    rcases ent with ⟨k, e⟩
    cases hk : bv_eqb k fd with
    | true =>
      have he := (LinuxProcessSemantics.Riscv.Prelude.bv_eqb_eq k fd).1 hk
      subst k
      simp only [List.filter_cons, hk, Bool.not_true, Bool.false_eq_true, ite_false,
        ih, fd_lookup_cons_neq fds fd e fd' (Ne.symm hne)]
    | false =>
      simp only [List.filter_cons, hk, Bool.not_false, ite_true, fd_lookup, ih]

theorem fd_lookup_insert_eq (fds : List (word × FdEntry)) (fd : word) (e : FdEntry) :
    fd_lookup (fd_insert fds fd e) fd = some e :=
  fd_lookup_cons_eq _ fd e

theorem fd_lookup_insert_neq (fds : List (word × FdEntry)) (fd : word) (e : FdEntry)
    (fd' : word) (hne : fd' ≠ fd) :
    fd_lookup (fd_insert fds fd e) fd' = fd_lookup fds fd' := by
  rw [fd_insert, fd_lookup_cons_neq _ fd e fd' (Ne.symm hne),
    fd_lookup_filter_neq fds fd fd' hne]

theorem fd_lookup_remove_neq (fds : List (word × FdEntry)) (fd fd' : word)
    (hne : fd' ≠ fd) : fd_lookup (fd_remove fds fd) fd' = fd_lookup fds fd' :=
  fd_lookup_filter_neq fds fd fd' hne

theorem fd_lookup_some_none_neq (fds : List (word × FdEntry)) (a b : word)
    (ea : FdEntry) (ha : fd_lookup fds a = some ea) (hb : fd_lookup fds b = none) :
    a ≠ b := by
  intro he
  subst b
  rw [ha] at hb
  cases hb

theorem free_fd_after_open (x y z : FdEntry) (fdin : word) (e : FdEntry) :
    ∃ w, fd_lookup (fd_insert
      [(Z_to_bv 64 0, x), (Z_to_bv 64 1, y), (Z_to_bv 64 2, z)] fdin e) w = none ∧
      bv_unsigned w < 2 ^ 31 := by
  by_cases h : fdin = Z_to_bv 64 3
  · subst fdin
    refine ⟨Z_to_bv 64 4, ?_, by decide⟩
    rw [fd_lookup_insert_neq _ _ _ _ (by decide)]
    rfl
  · refine ⟨Z_to_bv 64 3, ?_, by decide⟩
    rw [fd_lookup_insert_neq _ _ _ _ (Ne.symm h)]
    rfl

theorem filter_fd_cons_keep {B : Type u} (fds : List (word × B)) (k : word)
    (e : B) (fd : word) (hne : k ≠ fd) :
    ((k, e) :: fds).filter (fun p => !(bv_eqb p.1 fd)) =
      (k, e) :: fds.filter (fun p => !(bv_eqb p.1 fd)) := by
  simp only [List.filter_cons, bv_eqb_neq k fd hne, Bool.not_false, ite_true]

theorem filter_fd_cons_drop {B : Type u} (fds : List (word × B)) (fd : word) (e : B) :
    ((fd, e) :: fds).filter (fun p => !(bv_eqb p.1 fd)) =
      fds.filter (fun p => !(bv_eqb p.1 fd)) := by
  simp only [List.filter_cons, PropExec.bv_eqb_refl, Bool.not_true, Bool.false_eq_true, ite_false]

/-! ## File read/write arithmetic -/

theorem length_file_read (data : List byte) (off count : word) :
    (file_read data off count).length =
      min (word_to_nat count) (data.length - word_to_nat off) := by
  rw [file_read_unguarded, List.length_take, List.length_drop]

theorem file_read_nil (data : List byte) (off count : word)
    (h : data.length ≤ word_to_nat off) : file_read data off count = [] := by
  rw [file_read_unguarded, List.drop_eq_nil_of_le h, List.take_nil]

theorem file_write_append (data : List byte) (off : word) (bs : List byte)
    (hoff : word_to_nat off = data.length) : file_write data off bs = data ++ bs := by
  cases bs with
  | nil => simp only [file_write, List.append_nil]
  | cons b bs =>
    simp only [file_write, hoff, Nat.sub_self, List.replicate_zero, List.append_nil,
      List.take_length, List.drop_eq_nil_of_le (Nat.le_add_right data.length _)]

theorem firstn_add {A : Type u} (l : List A) (n m : Nat) :
    l.take (n + m) = l.take n ++ (l.drop n).take m := by
  exact List.take_add

theorem copy_step (data : List byte) (off count : word) :
    data.take (word_to_nat off) ++ file_read data off count =
      data.take (word_to_nat off +
        min (word_to_nat count) (data.length - word_to_nat off)) := by
  rw [file_read_unguarded, firstn_add]
  congr 1
  rw [← List.length_drop, firstn_min_length]

/-! ## C-string bridges through the merged read view -/

def mrb (segs : List Segment) (mem : word → Option byte) : word → Option byte :=
  fun a => match mem a with | some b => some b | none => seg_rom segs a

theorem ms_read_byte_mrb (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem : word → Option byte) :
    ms_read_byte (mkst regs pc mem (seg_rom segs)) = mrb segs mem := rfl

theorem ms_read_byte_rec_mrb (segs : List Segment) (regs : bvmap 5 word)
    (fr : bvmap 5 (BitVec 64)) (pc : word) (sv : Option word) (rv : Option word)
    (fc : BitVec 32) (mem : word → Option byte) :
    ms_read_byte {
      ms_regs := regs, ms_fregs := fr, ms_pc_val := pc,
      ms_svc_pending := sv, ms_resv := rv, ms_fcsr := fc,
      ms_mem := mem, ms_rom := seg_rom segs } = mrb segs mem := rfl

theorem mrb_first (segs : List Segment) (mem : word → Option byte) (a : word)
    (n : Nat) (b : byte) (rest : List byte)
    (h : rdn segs mem a (n + 1) = some (b :: rest)) : mrb segs mem a = some b := by
  unfold rdn at h
  split at h
  · split at h
    · cases h
      assumption
    · cases h
  · cases h

theorem rdn_tail (segs : List Segment) (mem : word → Option byte) (a : word)
    (n : Nat) (b : byte) (rest : List byte)
    (h : rdn segs mem a (n + 1) = some (b :: rest)) :
    rdn segs mem (a + 1) n = some rest := by
  unfold rdn at h
  split at h
  · split at h
    · cases h
      assumption
    · cases h
  · cases h

theorem read_cstr_aux_of_rdn (segs : List Segment) (str : List byte) (fuel : Nat)
    (mem : word → Option byte) (a : word) (hf : str.length < fuel)
    (hnz : Z_to_bv 8 0 ∉ str)
    (hr : rdn segs mem a (str.length + 1) = some (str ++ [Z_to_bv 8 0])) :
    read_cstr_aux (mrb segs mem) a fuel = CstrOk str := by
  induction str generalizing fuel a with
  | nil =>
    cases fuel with
    | zero => simp only [List.length_nil] at hf; omega
    | succ fuel =>
      have hb := mrb_first segs mem a 0 (Z_to_bv 8 0) [] hr
      simp only [read_cstr_aux, hb, PropExec.bv_eqb_refl, ite_true]
  | cons b str ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hb : b ≠ Z_to_bv 8 0 := fun he => hnz (List.mem_cons.mpr (Or.inl he.symm))
      have ht : Z_to_bv 8 0 ∉ str := fun h => hnz (List.mem_cons.mpr (Or.inr h))
      have hfirst := mrb_first segs mem a (str.length + 1) b (str ++ [Z_to_bv 8 0]) hr
      have htail := rdn_tail segs mem a (str.length + 1) b (str ++ [Z_to_bv 8 0]) hr
      simp only [read_cstr_aux, hfirst, bv_eqb_neq b (Z_to_bv 8 0) hb,
        Bool.false_eq_true, ite_false,
        ih fuel (a + 1) (by simp only [List.length_cons] at hf; omega) ht htail]

theorem read_cstr_of_rdn (segs : List Segment) (mem : word → Option byte) (a : word)
    (str : List byte) (hlen : str.length ≤ 4095) (hnz : Z_to_bv 8 0 ∉ str)
    (hr : rdn segs mem a (str.length + 1) = some (str ++ [Z_to_bv 8 0])) :
    read_cstr (mrb segs mem) a = CstrOk str :=
  read_cstr_aux_of_rdn segs str 4096 mem a (by omega) hnz hr

theorem read_cstr_aux_toolong_of_rdn (segs : List Segment) (fuel : Nat) (bs : List byte)
    (mem : word → Option byte) (a : word) (hlen : bs.length = fuel)
    (hnz : Z_to_bv 8 0 ∉ bs) (hr : rdn segs mem a fuel = some bs) :
    read_cstr_aux (mrb segs mem) a fuel = CstrTooLong := by
  induction fuel generalizing bs a with
  | zero => rfl
  | succ fuel ih =>
    cases bs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons b bs =>
      have hb : b ≠ Z_to_bv 8 0 := fun he => hnz (List.mem_cons.mpr (Or.inl he.symm))
      have ht : Z_to_bv 8 0 ∉ bs := fun h => hnz (List.mem_cons.mpr (Or.inr h))
      have hfirst := mrb_first segs mem a fuel b bs hr
      have htail := rdn_tail segs mem a fuel b bs hr
      simp only [read_cstr_aux, hfirst, bv_eqb_neq b (Z_to_bv 8 0) hb,
        Bool.false_eq_true, ite_false,
        ih bs (a + 1) (by simp only [List.length_cons] at hlen; omega) ht htail]

theorem read_cstr_toolong_of_rdn (segs : List Segment) (mem : word → Option byte)
    (a : word) (bs : List byte) (hlen : bs.length = 4096) (hnz : Z_to_bv 8 0 ∉ bs)
    (hr : rdn segs mem a 4096 = some bs) : read_cstr (mrb segs mem) a = CstrTooLong :=
  read_cstr_aux_toolong_of_rdn segs 4096 bs mem a hlen hnz hr

/-! ## Argument strings -/

theorem read_argv_cstr_k (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (av ev : List (List byte)) (k : Nat) (uid hw : word) (rnd : EntryDraw)
    (hk : k < av.length)
    (hnw : bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
      (cat_argv_ptr sp av ev k) ((av.getD k []).length + 1) =
        some (av.getD k [] ++ [Z_to_bv 8 0]) := by
  obtain ⟨pre, post, he, hlen⟩ := bsb_byte_k ph sp av ev k uid hw rnd hk
  have h := read_at_offset_image segs ph sp av ev uid hw rnd
    pre (av.getD k [] ++ [Z_to_bv 8 0]) post ((av.getD k []).length + 1)
    he (by rw [List.length_append]; rfl) hnw
  rw [hlen] at h
  rw [cat_argv_ptr_offset sp av ev k hk, cat_string_base, nat_to_word_add_merge]
  exact h

theorem read_argv_prefix_k (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (av ev : List (List byte)) (k n : Nat) (uid hw : word) (rnd : EntryDraw)
    (hk : k < av.length) (hn : n ≤ (av.getD k []).length)
    (hnw : bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
      (cat_argv_ptr sp av ev k) n = some ((av.getD k []).take n) := by
  obtain ⟨pre, post, he, hlen⟩ := bsb_byte_k ph sp av ev k uid hw rnd hk
  have h := read_at_offset_image segs ph sp av ev uid hw rnd
    pre ((av.getD k []).take n) (((av.getD k []).drop n ++ [Z_to_bv 8 0]) ++ post) n
    (by rw [he]; simp only [← List.append_assoc, List.take_append_drop])
    (by rw [List.length_take, Nat.min_eq_left hn]) hnw
  rw [hlen] at h
  rw [cat_argv_ptr_offset sp av ev k hk, cat_string_base, nat_to_word_add_merge]
  exact h

end LinuxProcessSemantics.Common.FileSim
