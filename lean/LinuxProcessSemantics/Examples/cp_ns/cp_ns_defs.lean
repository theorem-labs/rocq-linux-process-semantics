import LinuxProcessSemantics.Common.FileSim.Glue
import LinuxProcessSemantics.Common.FileSim.Open
import LinuxProcessSemantics.Common.FileSim.ReadWrite
import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.StreamExec
import LinuxProcessSemantics.Common.WallSim
import LinuxProcessSemantics.Common.StreamSim
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Examples.cp_ns.cp_ns_code
import LinuxProcessSemantics.Examples.cp_ns.SourceMemImage
import LinuxProcessSemantics.Examples.cp_ns.TargetMemImage

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Proof-side shared definitions for the copy example. Rocq section parameters
are explicit leading arguments; firstn/skipn are List.take/List.drop.
The open-flag mask uses the existing FileSim bitvector spelling of Z.ldiff.
The shared `u_len_word` theorem is imported from Common.WallSim. -/

namespace LinuxProcessSemantics.Examples.cp_ns.cp_ns_defs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.StreamExec
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Examples.cp_ns.SourceMemImage
open LinuxProcessSemantics.Examples.cp_ns.TargetMemImage
open LinuxProcessSemantics.Examples.cp_ns.cp_ns_code

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
open LinuxProcessSemantics.Common.FileSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.ErrEscape
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
open FdEntry

theorem delivered_writes_ne (buf : word) (bs : List byte) (hne : bs ≠ []) :
    delivered_writes buf bs = [(buf, bs)] := by
  cases bs with
  | nil => exact False.elim (hne rfl)
  | cons => rfl

theorem wtn_ntw (n : Nat) (hn : (n : Int) < 2^64) :
    word_to_nat (nat_to_word n) = n := by
  have h := u_ntw n hn
  change (nat_to_word n).toNat = n
  change ((nat_to_word n).toNat : Int) = (n : Int) at h
  omega

theorem wtn_len_word {A : Type} (l : List A) (hl : (l.length : Int) < 2^64) :
    word_to_nat (len_word l) = l.length := wtn_ntw l.length hl

theorem len_word_ntw {A : Type} (l : List A) :
    len_word l = nat_to_word l.length := rfl

theorem file_write_len_lb (data : List byte) (off : word) (bs : List byte)
    (hoff : bv_unsigned off ≤ (data.length : Int)) :
    bv_unsigned off + (bs.length : Int) ≤ (file_write data off bs).length := by
  have hn : (word_to_nat off : Int) = bv_unsigned off := rfl
  cases bs with
  | nil => simpa only [file_write, List.length_nil, Int.ofNat_zero, Int.add_zero] using hoff
  | cons b bs =>
    have hz : word_to_nat off - data.length = 0 := by omega
    simp only [file_write, hz, List.replicate_zero, List.append_nil,
      List.length_append, List.length_take, List.length_drop, List.length_cons]
    omega

theorem file_write_off_bound (data : List byte) (off : word) (bs : List byte)
    (hbs : (bs.length : Int) < 2^64) (hoff : bv_unsigned off ≤ (data.length : Int)) :
    bv_unsigned (off + len_word bs) ≤ (file_write data off bs).length := by
  have hl := file_write_len_lb data off bs hoff
  have hu := u_len_word bs hbs
  change (((off.toNat + (len_word bs).toNat) % 2^64 : Nat) : Int) ≤ _
  have hm := Nat.mod_le (off.toNat + (len_word bs).toNat) (2^64)
  change ((len_word bs).toNat : Int) = (bs.length : Int) at hu
  change (off.toNat : Int) + (bs.length : Int) ≤ _ at hl
  omega

theorem ntw_add (a b : Nat) :
    nat_to_word a + nat_to_word b = nat_to_word (a + b) := by
  simp only [nat_to_word, Z_to_bv, Int.natCast_add, BitVec.ofInt_add]

theorem wtn_1024 : word_to_nat (Z_to_bv 64 1024) = 1024 := rfl

theorem source_init_pc_val : SourceMemImage_init_pc = 0x1112c := rfl

theorem target_init_pc_val : TargetMemImage_init_pc = 0x1001190 := rfl

def cp_read_data (fs0 : Fs) (src dst : path) : List byte :=
  match fs_lookup (fs_set fs0 dst []) src with
  | some d => d
  | none => []

def cp_final_fs (fs0 : Fs) (src dst : path) : Fs :=
  fs_set fs0 dst (cp_read_data fs0 src dst)

def cp_outcomes (fs0 : Fs) (src dst : path) : word × Fs → Prop := fun o =>
  match fs_lookup fs0 src with
  | none => o = (Z_to_bv 64 3, fs0)
  | some _ => o = (Z_to_bv 64 3, fs0) ∨ o = (Z_to_bv 64 4, fs0) ∨
      (fs_under fs0 dst = false ∧ o = (Z_to_bv 64 0, cp_final_fs fs0 src dst))

theorem path_eqb_false_neq (p q : path) (h : path_eqb p q = false) : p ≠ q := by
  intro he
  subst q
  rw [path_eqb_refl] at h
  cases h

theorem cp_read_data_stable (fs0 : Fs) (src dst : path) (v : List byte)
    (hne : src ≠ dst) :
    fs_lookup (fs_set (fs_set fs0 dst []) dst v) src = fs_lookup fs0 src := by
  rw [fs_lookup_set_neq _ dst v src hne, fs_lookup_set_neq _ dst [] src hne]

theorem cp_final_collapse (fs0 : Fs) (src dst : path) :
    fs_set (fs_set fs0 dst []) dst (cp_read_data fs0 src dst) = cp_final_fs fs0 src dst :=
  fs_set_set _ _ _ _

theorem cp_read_data_lookup (fs0 : Fs) (src dst : path) (d0 : List byte)
    (h0 : fs_lookup fs0 src = some d0) :
    fs_lookup (fs_set fs0 dst []) src = some (cp_read_data fs0 src dst) := by
  unfold cp_read_data
  by_cases he : src = dst
  · subst dst
    rw [fs_lookup_set_eq]
  · rw [fs_lookup_set_neq _ _ _ _ he, h0]

theorem cp_lookup_src_k (fs0 : Fs) (src dst : path) (D : List byte) (k : Nat)
    (h0 : fs_lookup (fs_set fs0 dst []) src = some D) (_hk : k ≤ D.length) :
    fs_lookup (fs_set fs0 dst (D.take k)) src = some D := by
  by_cases he : src = dst
  · subst dst
    rw [fs_lookup_set_eq] at h0
    cases h0
    rw [List.take_nil, fs_lookup_set_eq]
  · rw [fs_lookup_set_neq _ _ _ _ he] at h0 ⊢
    exact h0

theorem cp_read_data_big_neq (fs0 : Fs) (src dst : path)
    (hbig : (2^64 : Int) ≤ ((cp_read_data fs0 src dst).length : Int)) : src ≠ dst := by
  intro he
  subst dst
  simp only [cp_read_data, fs_lookup_set_eq, List.length_nil] at hbig
  omega

theorem cp_read_data_neq (fs0 : Fs) (src dst : path) (d0 : List byte)
    (hne : src ≠ dst) (hsome : fs_lookup fs0 src = some d0) :
    cp_read_data fs0 src dst = d0 := by
  simp only [cp_read_data, fs_lookup_set_neq _ _ _ _ hne, hsome]

theorem cp_chunk_len (D : List byte) (k : Nat) (hk : (k : Int) < 2^64) :
    (file_read D (nat_to_word k) (Z_to_bv 64 1024)).length = min 1024 (D.length - k) := by
  rw [length_file_read, wtn_1024, wtn_ntw _ hk]

theorem cp_fs_write_step (fs0 : Fs) (dst : path) (D : List byte) (k : Nat)
    (hk : k ≤ D.length) (hD : (D.length : Int) < 2^64) :
    fs_set (fs_set fs0 dst (D.take k)) dst
      (file_write (D.take k) (nat_to_word k) (file_read D (nat_to_word k) (Z_to_bv 64 1024))) =
      fs_set fs0 dst (D.take (k + min 1024 (D.length - k))) := by
  rw [fs_set_set, file_write_append _ _ _ (by rw [wtn_ntw _ (by omega), List.length_take]; omega)]
  have h := copy_step D (nat_to_word k) (Z_to_bv 64 1024)
  rw [wtn_1024, wtn_ntw _ (by omega)] at h
  rw [h]

macro "model_simp" : tactic => `(tactic|
  simp only [with_fds, with_fs, m_fds, m_fs, m_halted])

/-- Deterministic silent regions, including uniquely resolving silent syscalls. -/
inductive dsil (segs : List Segment) : config → config → Prop where
  | dsil_refl (c) : dsil segs c c
  | dsil_instr (ms model ms' c'') :
      m_vm_lazy model = [] → ms.ms_svc_pending = none →
      RiscvSemantics.step segs ms = MachineOk ms' →
      dsil segs (.mkCfg ms' model) c'' → dsil segs (.mkCfg ms model) c''
  | dsil_sys (ms model x8 eff model' c'') :
      ms.ms_svc_pending = some x8 → m_halted model = none → m_vm_lazy model = [] →
      syscall_spec (sys_input segs ms x8) model (Ok eff model' []) →
      (∀ eff2 m2 evs2, syscall_spec (sys_input segs ms x8) model (Ok eff2 m2 evs2) →
        eff2 = eff ∧ m2 = model' ∧ evs2 = []) →
      (¬ syscall_spec (sys_input segs ms x8) model Unmodeled) →
      m_halted model' = none → m_vm_lazy model' = [] →
      dsil segs (.mkCfg (advance_past_svc (apply_effect ms eff)) model') c'' →
      dsil segs (.mkCfg ms model) c''

section Fdiv
variable (segs : List Segment)

theorem dsil_msteps (ms ms' : machine_state) (model : Model) (c'' : config)
    (h : msteps segs ms ms') (hlazy : m_vm_lazy model = [])
    (hd : dsil segs (.mkCfg ms' model) c'') : dsil segs (.mkCfg ms model) c'' := by
  induction h with
  | mst_refl => exact hd
  | mst_step ms ms1 ms2 hsvc hstep _ ih =>
    exact dsil.dsil_instr ms model ms1 c'' hlazy hsvc hstep (ih hd)

theorem dsil_halted (c c'' : config) (h : dsil segs c c'')
    (hh : m_halted c''.cfg_model = none) : m_halted c.cfg_model = none := by
  induction h with
  | dsil_refl => exact hh
  | dsil_instr _ _ _ _ _ _ _ _ ih => exact ih hh
  | dsil_sys _ _ _ _ _ _ _ hh0 _ _ _ _ _ _ _ _ => exact hh0

theorem dsil_lazy (c c'' : config) (h : dsil segs c c'')
    (hl : m_vm_lazy c''.cfg_model = []) : m_vm_lazy c.cfg_model = [] := by
  cases h with
  | dsil_refl => exact hl
  | dsil_instr _ _ _ _ hl0 _ _ _ => exact hl0
  | dsil_sys _ _ _ _ _ _ _ _ hl0 _ _ _ _ _ _ => exact hl0

def fdiv_resp (I : config → Prop) (X : word × Fs → Prop)
    (evs : List event) (st : step_to) : Prop :=
  evs = [] ∧ ∃ c', st = SNext c' ∧
    (I c' ∨ (m_halted c'.cfg_model = none ∧ m_vm_lazy c'.cfg_model = [] ∧
      ∃ U, to_fout segs c'.cfg_ms c'.cfg_model U ∧ (∀ o, U o → X o)))

def fdiv_ok (I : config → Prop) (X : word × Fs → Prop) : Prop :=
  ∀ c, I c → ∀ evs st, sstep segs c evs st → fdiv_resp segs I X evs st

theorem msteps_region_inv (ms anchor : machine_state) (model : Model)
    (evs : List event) (st : step_to) (hm : msteps segs ms anchor)
    (hlazy : m_vm_lazy model = []) (hss : sstep segs (.mkCfg ms model) evs st) :
    ms = anchor ∨ (evs = [] ∧ ∃ ms1, st = SNext (.mkCfg ms1 model) ∧
      msteps segs ms1 anchor) := by
  cases hm with
  | mst_refl => exact Or.inl rfl
  | mst_step ms ms1 anchor hsvc hstep hm =>
    obtain ⟨hevs, hst⟩ := sstep_instr_inv segs ms model ms1 evs st hlazy hsvc hstep hss
    exact Or.inr ⟨hevs, ms1, hst, hm⟩

theorem dsil_region_inv (A I : config → Prop) (X : word × Fs → Prop)
    (_hh : ∀ c, A c → m_halted c.cfg_model = none)
    (hlazy : ∀ c, A c → m_vm_lazy c.cfg_model = [])
    (hanchor : ∀ c, A c → ∀ evs st, sstep segs c evs st → fdiv_resp segs I X evs st)
    (hinto : ∀ c c'', dsil segs c c'' → A c'' → I c)
    (c c'' : config) (hd : dsil segs c c'') (ha : A c'')
    (evs : List event) (st : step_to) (hss : sstep segs c evs st) :
    fdiv_resp segs I X evs st := by
  cases hd with
  | dsil_refl => exact hanchor c ha evs st hss
  | dsil_instr ms model ms' c'' _ hsvc hstep hd =>
    obtain ⟨hevs, hst⟩ := sstep_instr_inv segs ms model ms' evs st
      (dsil_lazy segs _ _ hd (hlazy _ ha)) hsvc hstep hss
    exact ⟨hevs, _, hst, Or.inl (hinto _ _ hd ha)⟩
  | dsil_sys ms model x8 eff model' c'' hsvc hhm hmlazy _ huniq hne hh' hl' hd =>
    have hshape : ∀ e2 m2 ev2, syscall_spec (sys_input segs ms x8) model (Ok e2 m2 ev2) →
        ev2 = [] ∧ m_halted m2 = none ∧ m_vm_lazy m2 = [] := by
      intro e2 m2 ev2 hs
      obtain ⟨_, rfl, rfl⟩ := huniq e2 m2 ev2 hs
      exact ⟨rfl, hh', hl'⟩
    obtain ⟨eff2, m2, hs2, hevs, hst⟩ :=
      sstep_fsys_inv segs ms model x8 evs st hhm hmlazy hsvc hne hshape hss
    obtain ⟨rfl, rfl, _⟩ := huniq eff2 m2 [] hs2
    exact ⟨hevs, _, hst, Or.inl (hinto _ _ hd ha)⟩

theorem fdiv_star_only (I : config → Prop) (X : word × Fs → Prop)
    (hok : fdiv_ok segs I X) (c : config) (tr : List event) (c' : config)
    (hstar : star segs c tr c') (hi : I c) :
    tr = [] ∨ ∃ o, X o ∧ is_prefix tr (fout_trace o) := by
  induction hstar with
  | star_refl => exact Or.inl rfl
  | star_step c1 evs c2 tr2 c3 hss hstar ih =>
    obtain ⟨rfl, c2', hst, hcase⟩ := hok c1 hi evs _ hss
    cases hst
    simp only [List.nil_append]
    rcases hcase with hi2 | ⟨hh2, hlazy2, U, hto, hux⟩
    · exact ih hi2
    · obtain ⟨o, ho, hp⟩ := to_fout_star_only segs c2.cfg_ms c2.cfg_model U
        hto hh2 hlazy2 tr2 c3 hstar
      exact Or.inr ⟨o, hux o ho, hp⟩

theorem fdiv_star_region (I : config → Prop) (X : word × Fs → Prop)
    (hok : fdiv_ok segs I X) (c : config) (tr : List event) (c' : config)
    (hstar : star segs c tr c') (hi : I c) : I c' ∨ fon_path segs c' := by
  induction hstar with
  | star_refl => exact Or.inl hi
  | star_step c1 evs c2 tr2 c3 hss hstar ih =>
    obtain ⟨_, c2', hst, hcase⟩ := hok c1 hi evs _ hss
    cases hst
    rcases hcase with hi2 | ⟨hh2, hlazy2, U, hto, _⟩
    · exact ih hi2
    · exact Or.inr (star_fon_path segs c2 tr2 c3 (Or.inl ⟨hh2, hlazy2, U, hto⟩) hstar)

theorem fdiv_no_error (I : config → Prop) (X : word × Fs → Prop)
    (hok : fdiv_ok segs I X) (c : config) (hi : I c) : ¬ reaches_error segs c := by
  rintro ⟨tr, c', evs, hstar, hss⟩
  rcases fdiv_star_region segs I X hok c tr c' hstar hi with hi' | hop
  · obtain ⟨_, c'', hst, _⟩ := hok c' hi' evs _ hss
    cases hst
  · exact fon_path_no_error segs c' evs hop hss

end Fdiv

theorem source_avoids_ro (a : word) (n : Int) (ha : 0x13000 ≤ bv_unsigned a) :
    range_avoids_ro_segs source_segs (bv_unsigned a) n = true :=
  range_avoids_ro_above source_segs 0x13000 _ n (by decide +kernel) ha

theorem target_avoids_ro (a : word) (n : Int) (ha : 0x1002000 ≤ bv_unsigned a) :
    range_avoids_ro_segs target_segs (bv_unsigned a) n = true :=
  range_avoids_ro_above target_segs 0x1002000 _ n (by decide +kernel) ha

theorem source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true := by
  apply wseg_ok_backed source_segs SourceMemImage_segment_003 _ _
    [SourceMemImage_seg_bytes_003_chars]
  · rfl
  · decide +kernel
  · exact congrArg (fun x => [x]) SourceMemImage_seg_bytes_003_chars_eq
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
    (hlo : 0x13000 ≤ bv_unsigned a) (hhi : bv_unsigned a + (n : Int) ≤ 0x14000) :
    store_ok source_segs m a n = true :=
  store_ok_window source_segs m 0x13000 a 4096 n 0x13000 0x14000
    rfl rfl (by decide +kernel) source_data_wseg hlo hhi

theorem target_data_wseg : wseg_ok target_segs (0x1002000 : word) 4096 = true := by
  apply wseg_ok_backed target_segs TargetMemImage_segment_002 _ _
    [TargetMemImage_seg_bytes_002_chars]
  · rfl
  · decide +kernel
  · exact congrArg (fun x => [x]) TargetMemImage_seg_bytes_002_chars_eq
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
    (hlo : 0x1002000 ≤ bv_unsigned a) (hhi : bv_unsigned a + (n : Int) ≤ 0x1003000) :
    store_ok target_segs m a n = true :=
  store_ok_window target_segs m 0x1002000 a 4096 n 0x1002000 0x1003000
    rfl rfl (by decide +kernel) target_data_wseg hlo hhi


theorem source_buf_wseg : wseg_ok source_segs (0x13008 : word) (word_to_nat (Z_to_bv 64 1024)) = true := by
  apply wseg_ok_backed source_segs SourceMemImage_segment_003 _ _
    [SourceMemImage_seg_bytes_003_chars]
  · rfl
  · decide +kernel
  · exact congrArg (fun x => [x]) SourceMemImage_seg_bytes_003_chars_eq
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


theorem target_buf_wseg : wseg_ok target_segs (0x1002298 : word) (word_to_nat (Z_to_bv 64 1024)) = true := by
  apply wseg_ok_backed target_segs TargetMemImage_segment_002 _ _
    [TargetMemImage_seg_bytes_002_chars]
  · rfl
  · decide +kernel
  · exact congrArg (fun x => [x]) TargetMemImage_seg_bytes_002_chars_eq
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


/-- Resolution characterization used at a silent read anchor. -/
theorem read_file_uniq (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (p : path) (off : word) (data w : List byte)
    (Hno : bv_unsigned x8 = 63)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some (FdFile p off))
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = some w)
    (Hcnt : bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max)
    (_Hpos : 0 < bv_unsigned (ms_gpr ms 2))
    (Haok : access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true) :
    let bs := file_read data off (ms_gpr ms 2)
    let eff := mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) []
    let model' := with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
      (FdFile p (off + len_word bs))) model
    syscall_spec (sys_input segs ms x8) model (Ok eff model' []) ∧
    (∀ eff2 m2 evs2, syscall_spec (sys_input segs ms x8) model (Ok eff2 m2 evs2) →
      eff2 = eff ∧ m2 = model' ∧ evs2 = []) ∧
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled := by
  let bs := file_read data off (ms_gpr ms 2)
  have Hlen : (bs.length : Int) ≤ bv_unsigned (ms_gpr ms 2) := by
    dsimp only [bs]
    rw [length_file_read]
    have Hmin := Nat.min_le_left (word_to_nat (ms_gpr ms 2))
      (data.length - word_to_nat off)
    change ((min _ _ : Nat) : Int) ≤ ((word_to_nat (ms_gpr ms 2) : Nat) : Int)
    omega
  have HL : bv_unsigned (len_word bs) ≤ bv_unsigned (ms_gpr ms 2) := by
    have Hr := word_unsigned_range (ms_gpr ms 2)
    rw [len_word_unsigned bs (by omega)]
    exact Hlen
  have Hword : Z_to_bv 64 (bv_unsigned (ms_gpr ms 2)) = ms_gpr ms 2 := by
    simp only [Z_to_bv, bv_unsigned, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have Hreduce : ∀ eff, check_syscall (sys_input segs ms x8) eff model =
      match (generalizing := false) bs with
      | [] => check_ret_only eff (Z_to_bv 64 0)
          (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
            (FdFile p (off + len_word bs))) model) []
      | _ :: _ => match eff with
        | .mkEffectU ret [(a, bs')] [] [] [] [] =>
          if bv_eqb a (ms_gpr ms 1) && listN_eqb bs' bs && bv_eqb ret (len_word bs)
          then CheckOk (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
            (FdFile p (off + len_word bs))) model) [] else CheckReject
        | _ => CheckReject := by
    intro eff
    rw [check_syscall_63 segs ms x8 eff model Hno]
    simp only [check_read, Hfd32, Hfd, Haok, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Hfs, rw_count_clamp_of_rw _ Hcnt, Hword, in_wmem_si]
    rw [read_bytes_map_prefix _ _ _ _ _ HL Hw]
    rfl
  have Hchk : ∀ eff m' evs,
      check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ↔
      eff = mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) [] ∧
      m' = with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
        (FdFile p (off + len_word bs))) model ∧ evs = [] := by
    intro eff m' evs
    rw [Hreduce]
    cases Hbs : bs with
    | nil => exact check_ret_only_ok_iff _ _ _ _ _ _
    | cons b rest =>
      cases eff with
      | mkEffectU ret ws zs us cs copyins =>
        cases ws with
        | nil => simp only [mkEffect, delivered_writes, SyscallEffect.mkEffectU.injEq,
            reduceCtorEq, and_false, false_and]
        | cons aw ws =>
          rcases aw with ⟨a, bytes⟩
          cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
            simp only [mkEffect, delivered_writes, reduceCtorEq, SyscallEffect.mkEffectU.injEq,
              List.cons.injEq, Prod.mk.injEq, and_true, and_false, false_and]
          split
          next H =>
            simp only [Bool.and_eq_true] at H
            obtain ⟨⟨Ha, Hb⟩, Hr⟩ := H
            have Ha' := (bv_eqb_eq _ _).mp Ha
            have Hb' := (listN_eqb_eq _ _).mp Hb
            have Hr' := (bv_eqb_eq _ _).mp Hr
            subst a bytes ret
            simp only [check_result.CheckOk.injEq, true_and, eq_comm]
          next H =>
            simp only [reduceCtorEq, false_iff]
            rintro ⟨⟨rfl, rfl, rfl⟩, _, _⟩
            exact H (by simp only [LinuxProcessSemantics.Common.PropExec.bv_eqb_refl, listN_eqb_refl, Bool.and_self])
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms x8).in_sysno) := by
    rw [in_sysno_si, Hno]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · exact (check_syscall_ok_iff _ _ _ _ _ Hagree).mp ((Hchk _ _ _).mpr ⟨rfl, rfl, rfl⟩)
  · intro eff m' evs Hs
    exact (Hchk _ _ _).mp ((check_syscall_ok_iff _ _ _ _ _ Hagree).mpr Hs)
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hreduce] at H
    cases Hbs : bs with
    | nil =>
      rw [Hbs] at H
      exact check_ret_only_no_unmodeled _ _ _ _ H
    | cons b rest =>
      rw [Hbs] at H
      cases H

/-- Resolution characterization used at a silent write anchor. -/
theorem write_file_uniq (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (p : path) (off : word) (data bs : List byte)
    (Hno : bv_unsigned x8 = 64)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some (FdFileW p off))
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hrd : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some bs)
    (Hcnt : bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hgap : (!modeled_file_gap data off bs) = false)
    (Hnz : w_is0 (ms_gpr ms 2) = false) :
    let eff := with_copyins [(ms_gpr ms 1, bs.length)] (mkEffect (ms_gpr ms 2) [] [])
    let model' := with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
      (FdFileW p (off + ms_gpr ms 2)))
      (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)
    syscall_spec (sys_input segs ms x8) model (Ok eff model' []) ∧
    (∀ eff2 m2 evs2, syscall_spec (sys_input segs ms x8) model (Ok eff2 m2 evs2) →
      eff2 = eff ∧ m2 = model' ∧ evs2 = []) ∧
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled := by
  have Hrb : read_bytes_map (sys_input segs ms x8).in_mem
      (ms_gpr ms 1) (ms_gpr ms 2) = some bs := Hrd
  have Hlen := read_bytes_map_length _ _ _ _ Hrb
  have Hret : len_word bs = ms_gpr ms 2 := by
    rw [len_word, Hlen]
    simp only [Z_to_bv, bv_unsigned, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have Hne : bs.length ≠ 0 := by
    intro Hz
    have Hzero : ms_gpr ms 2 = Z_to_bv 64 0 := by
      rw [← Hret, len_word, Hz]
      rfl
    have Htrue : w_is0 (ms_gpr ms 2) = true := by
      rw [Hzero]; exact LinuxProcessSemantics.Common.PropExec.bv_eqb_refl _
    rw [Hnz] at Htrue
    cases Htrue
  have Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model =
      check_ret_only_copyins [(ms_gpr ms 1, bs.length)] eff (ms_gpr ms 2)
        (with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (FdFileW p (off + ms_gpr ms 2)))
          (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) [] := by
    intro eff
    rw [check_syscall_64 segs ms x8 eff model Hno]
    have Hbeq : (bs.length == 0) = false := by
      rw [beq_eq_false_iff_ne]
      exact Hne
    simp only [check_write, Hfd32, Hfd, rw_range_in_range _ _ Hcnt,
      Bool.false_eq_true, ↓reduceIte,
      write_source_of_rw _ _ _ Hcnt, readable_bytes_full _ _ _ _ Hrb,
      Hfs, unreadable_source_past_eof, Hnz, Hbeq,
      Bool.not_false, Bool.true_and, Bool.false_and, Hgap, Hret]
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms x8).in_sysno) := by
    rw [in_sysno_si, Hno]; rfl
  refine ⟨?_, ?_, ?_⟩
  · apply (check_syscall_ok_iff _ _ _ _ _ Hagree).mp
    rw [Hchk, check_ret_only_copyins_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff m' evs Hs
    have H := (check_syscall_ok_iff _ _ _ _ _ Hagree).mpr Hs
    rw [Hchk, check_ret_only_copyins_ok_iff] at H
    exact H
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hchk] at H
    exact check_ret_only_copyins_no_unmodeled _ _ _ _ _ H

theorem open_rd_branches (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (p : path) (d : List byte)
    (Hno : bv_unsigned x8 = 56) (Hdirfd : ms_gpr ms 0 = AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hfl : bv_unsigned (bv_and (ms_gpr ms 2)
      (bv_not (Z_to_bv 64 open_ignored_flags))) = 0)
    (Hdot : openat_plain_name p = true)
    (Hfs : fs_lookup (m_fs model) p = some d) :
    let mk := fun fd => with_fds (fd_insert (m_fds model) fd
      (FdFile p (Z_to_bv 64 0)))
      model
    (¬ syscall_spec (sys_input segs ms x8) model Unmodeled) ∧
    (∀ e, e ∈ openat_errnos → syscall_spec (sys_input segs ms x8) model
      (Ok (with_copyins (open_copyins ms) (mkEffect (errno_ret e) [] [])) model [])) ∧
    (∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
      syscall_spec (sys_input segs ms x8) model
        (Ok (with_copyins (open_copyins ms) (mkEffect fd [] [])) (mk fd) [])) ∧
    (∀ eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) →
      evs = [] ∧ ((∃ e, e ∈ openat_errnos ∧
        eff = with_copyins (open_copyins ms) (mkEffect (errno_ret e) [] []) ∧ m' = model) ∨
      (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model) ∧
        eff = with_copyins (open_copyins ms) (mkEffect fd [] []) ∧ m' = mk fd))) := by
  dsimp only
  have Hchk := openat_rd_check segs ms x8 model p d Hno Hdirfd Hpath Hpe Hfl Hdot Hfs
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms x8).in_sysno) := by
    rw [in_sysno_si, Hno]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hchk] at H
    exact check_open_result_copyins_never_unmodeled _ _ _ _ H
  · intro e He
    apply (check_syscall_ok_iff _ _ _ _ _ Hagree).mp
    rw [Hchk, check_open_result_copyins_ok_iff]
    exact Or.inl ⟨e, He, rfl, rfl, rfl⟩
  · intro fd Hlk Heq
    apply (check_syscall_ok_iff _ _ _ _ _ Hagree).mp
    rw [Hchk, check_open_result_copyins_ok_iff]
    exact Or.inr ⟨fd, Hlk, Heq, rfl, rfl, rfl⟩
  · intro eff m' evs Hs
    have H := (check_syscall_ok_iff _ _ _ _ _ Hagree).mpr Hs
    rw [Hchk, check_open_result_copyins_ok_iff] at H
    rcases H with ⟨e, He, Heff, Hm, Hevs⟩ | ⟨fd, Hlk, Heq, Heff, Hm, Hevs⟩
    · exact ⟨Hevs, Or.inl ⟨e, He, Heff, Hm⟩⟩
    · exact ⟨Hevs, Or.inr ⟨fd, Hlk, Heq, Heff, Hm⟩⟩

theorem open_wr_branches (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (p : path)
    (Hno : bv_unsigned x8 = 56) (Hdirfd : ms_gpr ms 0 = AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hfl : bv_unsigned (bv_and (ms_gpr ms 2)
      (bv_not (Z_to_bv 64 open_ignored_flags))) = wr_create_flags)
    (Hdot : openat_plain_name p = true)
    (Hun : fs_under (m_fs model) p = false) :
    let mk := fun fd => with_fds (fd_insert (m_fds model) fd
      (FdFileW p (Z_to_bv 64 0)))
      (with_fs (fs_set (m_fs model) p []) model)
    (¬ syscall_spec (sys_input segs ms x8) model Unmodeled) ∧
    (∀ e, e ∈ openat_errnos → syscall_spec (sys_input segs ms x8) model
      (Ok (with_copyins (open_copyins ms) (mkEffect (errno_ret e) [] [])) model [])) ∧
    (∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
      syscall_spec (sys_input segs ms x8) model
        (Ok (with_copyins (open_copyins ms) (mkEffect fd [] [])) (mk fd) [])) ∧
    (∀ eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) →
      evs = [] ∧ ((∃ e, e ∈ openat_errnos ∧
        eff = with_copyins (open_copyins ms) (mkEffect (errno_ret e) [] []) ∧ m' = model) ∨
      (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model) ∧
        eff = with_copyins (open_copyins ms) (mkEffect fd [] []) ∧ m' = mk fd))) := by
  dsimp only
  have Hchk := openat_wr_check segs ms x8 model p Hno Hdirfd Hpath Hpe Hfl Hdot Hun
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms x8).in_sysno) := by
    rw [in_sysno_si, Hno]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hchk] at H
    exact check_open_result_copyins_never_unmodeled _ _ _ _ H
  · intro e He
    apply (check_syscall_ok_iff _ _ _ _ _ Hagree).mp
    rw [Hchk, check_open_result_copyins_ok_iff]
    exact Or.inl ⟨e, He, rfl, rfl, rfl⟩
  · intro fd Hlk Heq
    apply (check_syscall_ok_iff _ _ _ _ _ Hagree).mp
    rw [Hchk, check_open_result_copyins_ok_iff]
    exact Or.inr ⟨fd, Hlk, Heq, rfl, rfl, rfl⟩
  · intro eff m' evs Hs
    have H := (check_syscall_ok_iff _ _ _ _ _ Hagree).mpr Hs
    rw [Hchk, check_open_result_copyins_ok_iff] at H
    rcases H with ⟨e, He, Heff, Hm, Hevs⟩ | ⟨fd, Hlk, Heq, Heff, Hm, Hevs⟩
    · exact ⟨Hevs, Or.inl ⟨e, He, Heff, Hm⟩⟩
    · exact ⟨Hevs, Or.inr ⟨fd, Hlk, Heq, Heff, Hm⟩⟩

theorem open_wr_isdir (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (p : path)
    (Hno : bv_unsigned x8 = 56) (Hdirfd : ms_gpr ms 0 = AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hfl : bv_unsigned (bv_and (ms_gpr ms 2)
      (bv_not (Z_to_bv 64 open_ignored_flags))) = wr_create_flags)
    (Hdot : openat_plain_name p = true) (Hun : fs_under (m_fs model) p = true) :
    let eff := with_copyins (open_copyins ms) (mkEffect (errno_ret EISDIR) [] [])
    syscall_spec (sys_input segs ms x8) model (Ok eff model []) ∧
    (∀ eff2 m2 evs2, syscall_spec (sys_input segs ms x8) model (Ok eff2 m2 evs2) →
      eff2 = eff ∧ m2 = model ∧ evs2 = []) ∧
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled := by
  have Hchk := openat_wr_isdir_check segs ms x8 model p Hno Hdirfd Hpath Hpe Hfl Hdot Hun
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms x8).in_sysno) := by
    rw [in_sysno_si, Hno]; rfl
  refine ⟨?_, ?_, ?_⟩
  · apply (check_syscall_ok_iff _ _ _ _ _ Hagree).mp
    rw [Hchk, check_ret_only_copyins_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff2 m2 evs2 Hs
    have H := (check_syscall_ok_iff _ _ _ _ _ Hagree).mpr Hs
    rw [Hchk, check_ret_only_copyins_ok_iff] at H
    exact H
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hchk] at H
    exact check_ret_only_copyins_no_unmodeled _ _ _ _ _ H

theorem alloc_fd_lt_2_31 (fds : List (word × FdEntry)) : bv_unsigned (alloc_fd fds) < 2^31 := by
  have h := alloc_fd_le fds
  omega

theorem openat_wr_dot_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (p : path)
    (Hno : bv_unsigned x8 = 56) (Hdirfd : ms_gpr ms 0 = AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hfl : bv_unsigned (bv_and (ms_gpr ms 2)
      (bv_not (Z_to_bv 64 open_ignored_flags))) = wr_create_flags)
    (Hdot : path_eqb p dot_path = true) (eff : SyscallEffect) :
    check_syscall (sys_input segs ms x8) eff model =
      check_ret_only_copyins (open_copyins ms) eff (errno_ret EISDIR) model [] := by
  have Hdr : path_is_dirref p = true := by simp only [path_is_dirref, Hdot, Bool.true_or]
  have Hunw := path_is_dirref_no_slash p Hdr
  rw [check_syscall_56 segs ms x8 eff model Hno]
  simp only [check_openat, modeled_open_flags_wr _ Hfl, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, check_openat_body, in_mem_si, Hpath, Hpe, Hdirfd]
  have Hfd : bv_eqb (fd32 AT_FDCWD) AT_FDCWD32 = true := by decide
  have Hwr : (wr_create_flags == (0 : Int)) = false := by decide
  simp only [Hfd, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    check_openat_resolved, Hunw, Hfl, Hwr, beq_self_eq_true, check_openat_create, Hdr, Bool.true_or]
  exact check_copyins_after_ret_only (open_copyins ms) eff (errno_ret EISDIR) model []

theorem openat_rd_dot_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (p : path)
    (Hno : bv_unsigned x8 = 56) (Hdirfd : ms_gpr ms 0 = AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hfl : bv_unsigned (bv_and (ms_gpr ms 2)
      (bv_not (Z_to_bv 64 open_ignored_flags))) = 0)
    (Hdot : path_eqb p dot_path = true) (eff : SyscallEffect) :
    check_syscall (sys_input segs ms x8) eff model =
      check_open_result_copyins (open_copyins ms) eff model
        (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model) := by
  have Hdr : path_is_dirref p = true := by simp only [path_is_dirref, Hdot, Bool.true_or]
  have Hunw := path_is_dirref_no_slash p Hdr
  rw [check_syscall_56 segs ms x8 eff model Hno]
  simp only [check_openat, modeled_open_flags_rd _ Hfl, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, check_openat_body, in_mem_si, Hpath, Hpe, Hdirfd]
  have Hfd : bv_eqb (fd32 AT_FDCWD) AT_FDCWD32 = true := by decide
  simp only [Hfd, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    check_openat_resolved, Hunw, Hfl, beq_self_eq_true, check_openat_read, Hdr]
  unfold check_open_result_copyins open_copyins
  cases Hresult : check_open_result (clear_copyins eff) model
    (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model) with
  | CheckReject => rfl
  | CheckOk m evs => rfl
  | CheckUnmodeled => exact False.elim (check_open_result_never_unmodeled _ _ _ Hresult)

theorem read_dir_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (Hno : bv_unsigned x8 = 63)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some FdDir)
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hdr : (!access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2))) = false)
    (eff : SyscallEffect) :
    check_syscall (sys_input segs ms x8) eff model = check_ret_only eff (errno_ret EISDIR) model [] := by
  rw [check_syscall_63 segs ms x8 eff model Hno]
  simp only [check_read, Hfd32, Hfd, Hdr, Bool.false_eq_true, ↓reduceIte]

theorem tfo_open_wr_dot_rec (segs : List Segment) (regs : bvmap 5 word)
    (pc : word) (mem : word → Option byte) (model : Model) (p : path)
    (U : (word × Fs) → Prop)
    (H17 : bv_unsigned (getr regs 17) = 56)
    (H10 : reg_get regs 10 = AT_FDCWD) (Hfl : bv_unsigned (bv_and (reg_get regs 12)
      (bv_not (Z_to_bv 64 open_ignored_flags))) = wr_create_flags)
    (Hpath : read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hdot : path_eqb p dot_path = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs
      (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model U) :
    to_fout segs {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
      model U := by
  let ms : machine_state := {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
  have Hchk : ∀ eff, check_syscall (sys_input segs ms (getr regs 17)) eff model =
      check_ret_only_copyins (open_copyins ms) eff (errno_ret EISDIR) model [] := by
    intro eff
    exact openat_wr_dot_check segs ms (getr regs 17) model p H17 H10 Hpath Hpe Hfl Hdot eff
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms (getr regs 17)).in_sysno) := by
    rw [in_sysno_si, H17]
    rfl
  refine tfo_sys_det segs ms model (getr regs 17)
    (with_copyins (open_copyins ms) (mkEffect (errno_ret EISDIR) [] [])) model U
    rfl ?_ ?_ ?_ Hh Hlazy ?_
  · apply check_syscall_sound_ok
    rw [Hchk, check_ret_only_copyins_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff m evs Hs
    have H := check_syscall_complete_ok _ _ _ _ _ Hagree Hs
    rw [Hchk, check_ret_only_copyins_ok_iff] at H
    exact H
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hchk] at H
    exact check_ret_only_copyins_no_unmodeled _ _ _ _ _ H
  · simpa only [ms, adv_eff_ret_copyins] using Hcont


theorem tfo_read_dir_rec (segs : List Segment) (regs : bvmap 5 word)
    (pc : word) (mem : word → Option byte) (model : Model) (U : word × Fs → Prop)
    (H17 : bv_unsigned (getr regs 17) = 63)
    (Hfd : fd_lookup (m_fds model) (reg_get regs 10) = some FdDir)
    (Hfd32 : fd32 (reg_get regs 10) = reg_get regs 10)
    (Hdr : (!access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12))) = false)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs
      (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model U) :
    to_fout segs {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs } model U := by
  let ms : machine_state := {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
  have Hchk := read_dir_check segs ms (getr regs 17) model H17 Hfd Hfd32 Hdr
  have Hagree : lookups_agree_at (bv_unsigned (sys_input segs ms (getr regs 17)).in_sysno) := by
    rw [in_sysno_si, H17]
    rfl
  refine tfo_sys_det segs ms model (getr regs 17)
    (mkEffect (errno_ret EISDIR) [] []) model U
    rfl ?_ ?_ ?_ Hh Hlazy ?_
  · apply check_syscall_sound_ok
    rw [Hchk, check_ret_only_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff m evs Hs
    have H := check_syscall_complete_ok _ _ _ _ _ Hagree Hs
    rw [Hchk, check_ret_only_ok_iff] at H
    exact H
  · intro Hs
    have H := check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []) Hs
    rw [Hchk] at H
    exact check_ret_only_no_unmodeled _ _ _ _ H
  · simpa only [ms, adv_eff_ret] using Hcont


theorem tfo_open_rd_dot_rec (segs : List Segment) (regs : bvmap 5 word)
    (pc : word) (mem : word → Option byte) (model : Model) (p : path)
    (Te : Int → (word × Fs) → Prop) (Ts : word → (word × Fs) → Prop)
    (U : (word × Fs) → Prop)
    (H17 : bv_unsigned (getr regs 17) = 56)
    (H10 : reg_get regs 10 = AT_FDCWD) (H12 : reg_get regs 12 = Z_to_bv 64 0)
    (Hpath : read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hdot : path_eqb p dot_path = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Herr : ∀ e, e ∈ openat_errnos →
      to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs))
        model (Te e))
    (Hok : ∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
      to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
        (with_fds (fd_insert (m_fds model) fd FdDir) model) (Ts fd))
    (HU : ∀ o, U o ↔ ((∃ e, e ∈ openat_errnos ∧ Te e o) ∨
      (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model) ∧ Ts fd o))) :
    to_fout segs {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
      model U := by
  let ms : machine_state := {
      ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := Z_to_bv 32 0,
      ms_mem := mem, ms_rom := seg_rom segs }
  refine tfo_open_core segs ms model (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model)
    (getr regs 17) (open_copyins ms) Te Ts U rfl Hh Hlazy ?_ ?_ ?_ ?_ HU
  · intro eff
    apply openat_rd_dot_check segs ms (getr regs 17) model p H17 H10 Hpath Hpe
      ?_ Hdot eff
    change bv_unsigned (bv_and (reg_get regs 12) (bv_not (Z_to_bv 64 open_ignored_flags))) = 0
    rw [H12]
    decide
  · intro fd
    exact ⟨Hh, Hlazy⟩
  · intro e HIn
    simpa only [ms, adv_eff_ret_copyins] using Herr e HIn
  · intro fd Hlk Heq
    simpa only [ms, adv_eff_ret_copyins] using Hok fd Hlk Heq


end LinuxProcessSemantics.Examples.cp_ns.cp_ns_defs
