import LinuxProcessSemantics.Common.DrainAlg
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.StreamExec

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b
-/

/-! Mirrors `theories/Examples/arena_tee_ns/arena_tee_ns_defs.v`.
Rocq `Z` becomes `Int`, and `nat` and `N` become `Nat`; `firstn`, `skipn`
and `nth` become `List.take`, `List.drop` and `List.getD`. Arithmetic tactics
are replaced by `omega`, rewriting and closed computation. The retry-loop
proof uses `to_wall_mutind`, the Lean twin of Rocq's combined scheme.
-/

namespace LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_defs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.MmapSim
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.ShapeAlg
open LinuxProcessSemantics.Common.DrainAlg
open LinuxProcessSemantics.Common.ShapeAlg.realizes

/-- The arena is one page and the header is eight bytes, so the drain
capacity is `4096 - 8`. Kept as a `Nat` because DrainAlg's capacity is a `Nat`. -/
def cap : Nat := 4088

theorem Hcap_lt : (cap : Int) < 2 ^ 64 := by decide

/-- Every read asks for `cap - |acc|` bytes. One page bounds all of them,
so the model evaluates each one (`rw_bytes_max` is 131072). -/
theorem Hcap_mod : (cap : Int) ≤ rw_bytes_max := by decide

/-- Eight lowercase hex digits, most significant nibble first, of the low
32 bits. The source packs four digits into each word; the target stores
individual bytes. Only the resulting bytes matter here. -/
def hex_digit (v : Nat) : byte :=
  if v < 10 then Z_to_bv 8 ((48 + v : Nat) : Int)
  else Z_to_bv 8 ((87 + v : Nat) : Int)

def nib (n k : Nat) : Nat := (n / 16 ^ k) % 16

def hdr8 (n : Nat) : List byte :=
  [hex_digit (nib n 7), hex_digit (nib n 6),
   hex_digit (nib n 5), hex_digit (nib n 4),
   hex_digit (nib n 3), hex_digit (nib n 2),
   hex_digit (nib n 1), hex_digit (nib n 0)]

theorem hdr8_length (n : Nat) : (hdr8 n).length = 8 := rfl

/-- The successful run's single buffer: a header for the drained count,
followed by those bytes. -/
def arena_out (bs : List byte) : List byte := hdr8 bs.length ++ bs

theorem arena_out_length (bs : List byte) : (arena_out bs).length = 8 + bs.length := by
  rw [arena_out, List.length_append, hdr8_length]

/-- The header plus at most `cap` drained bytes fits one page, so the model
evaluates the write that emits it. -/
theorem arena_out_modeled (bs : List byte) (H : bs.length ≤ cap) :
    bufs_modeled [arena_out bs] := by
  intro b Hb
  simp only [List.mem_singleton] at Hb
  subst b
  unfold buf_modeled
  rw [arena_out_length]
  unfold cap at H
  unfold rw_bytes_max
  omega

/-- The output channel is 2, which requires `t_writes_ch`. -/
def ch2 : word := Z_to_bv 64 2
def ch0 : word := Z_to_bv 64 0

/-- The tail: one write of `arena_out bs` on channel 2, then exit 0. -/
def arena_tail (fs0 : Fs.Fs) (bs : List byte) : TSet :=
  t_writes_ch ch2 [arena_out bs] (t_exit (Z_to_bv 64 0) fs0)

/-- The failure tail: no output, exit 1. -/
def arena_fail (fs0 : Fs.Fs) : TSet :=
  t_writes [] (t_exit (Z_to_bv 64 1) fs0)

/-- The whole behavior, in the shape delivered by Rocq's `rz_mmap_drain`:
mmap failure or a successful bounded drain followed by its tail. -/
def arena_outcomes (fs0 : Fs.Fs) (stdin0 : InputStream) : TSet :=
  t_alt2 (arena_fail fs0) (t_drain cap (arena_tail fs0) cap stdin0 [])

/-- The collapsed form: chunking disappears and the tail is a function
of the input. -/
def arena_spec (fs0 : Fs.Fs) (stdin0 : InputStream) : TSet :=
  t_alt2 (arena_fail fs0)
    (t_emit ((stream_firstn stdin0 cap).map (ReadEv ch0))
      (arena_tail fs0 (stream_firstn stdin0 cap)))

/-- The tail contains the empty trace, automatically true of realized
shapes, but needed here by drain collapse as a fact about trace sets alone. -/
theorem arena_tail_ne (fs0 : Fs.Fs) (acc : List byte) : arena_tail fs0 acc [] :=
  t_emit_has_nil _ _

/-- Drain collapse removes the nondeterministic read chunking without
changing either outcome's trace-prefix set. -/
theorem arena_outcomes_spec (fs0 : Fs.Fs) (stdin0 : InputStream) :
    t_eq (arena_outcomes fs0 stdin0) (arena_spec fs0 stdin0) := by
  apply t_alt2_cong
  · exact t_eq_refl _
  · exact t_drain_top_collapse cap Hcap_lt (arena_tail fs0) (arena_tail_ne fs0) stdin0

/-- Both binaries emit through a retry loop. Replaying the channel-1
mutual proof with `node_write_ch` makes its full-buffer trace independent
of how the environment chunks delivery on channel 2. -/
theorem rz_wall_ch_mut (segs : List Segment) (fd ch : word) (model : Model)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fdchan fd ch model) (H32 : fd32 fd = fd) :
    (∀ ms rest k, to_wall segs fd ms rest k →
      buf_modeled rest → ∀ T : TSet, T [] →
      (∀ ms', k ms' → realizes segs (config.mkCfg ms' model) T) →
      realizes segs (config.mkCfg ms model) (t_emit (rest.map (WriteEv ch)) T)) ∧
    (∀ ms rest k, to_wall_tail segs fd ms rest k →
      buf_modeled rest → ∀ T : TSet, T [] →
      (∀ ms', k ms' → realizes segs (config.mkCfg ms' model) T) →
      realizes segs (config.mkCfg ms model) (t_emit (rest.map (WriteEv ch)) T)) := by
  apply to_wall_mutind segs fd
    (fun ms rest k => buf_modeled rest → ∀ T : TSet, T [] →
      (∀ ms', k ms' → realizes segs (config.mkCfg ms' model) T) →
      realizes segs (config.mkCfg ms model) (t_emit (rest.map (WriteEv ch)) T))
    (fun ms rest k => buf_modeled rest → ∀ T : TSet, T [] →
      (∀ ms', k ms' → realizes segs (config.mkCfg ms' model) T) →
      realizes segs (config.mkCfg ms model) (t_emit (rest.map (WriteEv ch)) T))
  · intro ms x8 rest k Hsvc Hno Hg Hr Hnb _ IH Hbm T HT Hk
    refine rz_conseq _ _ _ (rz_node _ (wr_index rest)
      (fun i => (rest.take i.val).map (WriteEv ch))
      (fun i => config.mkCfg (advance_past_svc (set_gpr0 ms (len_word (rest.take i.val)))) model)
      (fun i => t_emit ((rest.drop i.val).map (WriteEv ch)) T)
      (wr_full rest Hnb)
      (node_write_ch segs ms model fd ch x8 rest Hh Hlazy Hfd H32 Hsvc Hno Hg Hr Hbm Hnb)
      ?_) (t_alt_wall _ rest T HT Hnb)
    exact fun i => IH i.val i.property.1 i.property.2 (buf_modeled_skipn i.val rest Hbm) T HT Hk
  · intro ms k Hk _ T HT Hcont
    exact rz_conseq _ _ _ (Hcont ms Hk) (t_eq_sym _ _ (t_emit_nil_eq T HT))
  · intro ms rest k _ _ IH Hbm T HT Hk
    exact IH Hbm T HT Hk
  · intro ms ms' rest k Hsvc Hstep _ IH Hbm T HT Hk
    exact rz_step segs ms model ms' _ Hh Hlazy Hsvc Hstep (IH Hbm T HT Hk)

/-- The channel-parametric `ShapeAlg.wall_realizes`: a retry-loop
exit-after-writes run realizes the full-delivery shape `t_writes_ch`. -/
theorem wall_realizes_ch (segs : List Segment) (fd ch : word) (ms : machine_state)
    (model : Model) (bufs : List (List byte)) (code : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fdchan fd ch model) (H32 : fd32 fd = fd)
    (Hw : to_wallexit segs fd bufs code ms) (Hbm : bufs_modeled bufs) :
    realizes segs (config.mkCfg ms model) (t_writes_ch ch bufs (t_exit code (m_fs model))) := by
  induction bufs generalizing ms with
  | nil => exact exitline_realizes segs ms code model Hw Hh Hlazy
  | cons buf rest IH =>
    obtain ⟨_, Ht⟩ := Hw
    have Hb : buf_modeled buf := Hbm buf (List.mem_cons_self ..)
    have Hbs : bufs_modeled rest := fun b Hb => Hbm b (List.mem_cons_of_mem _ Hb)
    rw [t_writes_ch_cons]
    exact (rz_wall_ch_mut segs fd ch model Hh Hlazy Hfd H32).2 ms buf _ Ht Hb _
      (t_writes_ch_exit_has_nil _ rest code _) (fun ms' Hk => IH ms' Hk Hbs)

theorem page_round_up_Z_4096 : page_round_up_Z 4096 = 4096 := by decide

theorem pru_4096 : page_round_up (Z_to_bv 64 4096) = Z_to_bv 64 4096 := by decide

theorem nib_lt16 (n k : Nat) : nib n k < 16 := Nat.mod_lt _ (by decide)

/-- The digit's ASCII code as an integer. -/
def digZ (n k : Nat) : Int :=
  if nib n k < 10 then 48 + (nib n k : Int) else 87 + (nib n k : Int)

theorem digZ_range (n k : Nat) : 48 ≤ digZ n k ∧ digZ n k < 103 := by
  have H := nib_lt16 n k
  unfold digZ
  split <;> omega

theorem hex_digit_digZ (n k : Nat) : hex_digit (nib n k) = Z_to_bv 8 (digZ n k) := by
  unfold hex_digit digZ
  split <;> congr 1 <;> omega

/-- The low byte of the 64-bit digit value is the header byte. -/
theorem digb (n k : Nat) :
    Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (digZ n k))) = hex_digit (nib n k) := by
  have H := digZ_range n k
  rw [u_Z2bv _ (by omega) (by omega), hex_digit_digZ]

theorem nib_Z (n k : Nat) :
    (nib n k : Int) = (n : Int) / Z_pow 2 (4 * (k : Int)) % 16 := by
  have hp : (16 : Nat) ^ k = 2 ^ (4 * k) := by
    rw [Nat.pow_mul]
  have he : (4 * (k : Int)) = ((4 * k : Nat) : Int) := by omega
  rw [he]
  change ((n / 16 ^ k % 16 : Nat) : Int) = (n : Int) / (2 : Int) ^ (4 * k) % 16
  rw [hp, Int.natCast_emod, Int.natCast_ediv, Int.natCast_pow]
  rfl

/-- The machine's `(n >> s) & 15` is the nibble for `s = 4k`. -/
theorem dig_val (n k : Nat) (s : Int) (Hn : n ≤ cap) (Hk : k ≤ 7)
    (Hs : s = 4 * (k : Int)) :
    v_andi (v_srl (nat_to_word n) (Z_to_bv 64 s)) 15 =
      Z_to_bv 64 (nib n k : Int) := by
  subst s
  unfold v_srl v_andi
  rw [u_Z2bv (4 * (k : Int)) (by omega) (by omega),
    Int.emod_eq_of_lt (show 0 ≤ 4 * (k : Int) by omega) (show 4 * (k : Int) < 64 by omega),
    u_ntw n (by unfold cap at Hn; omega)]
  have hr := Z_shiftr_range (n : Int) (4 * (k : Int))
    ⟨by omega, by unfold cap at Hn; omega⟩ (by omega)
  rw [u_Z2bv _ hr.1 hr.2]
  have hshift : Z_shiftl (n : Int) (-(4 * (k : Int))) = ((n >>> (4 * k) : Nat) : Int) := by
    have he : 4 * (k : Int) = ((4 * k : Nat) : Int) := by omega
    rw [he]
    generalize 4 * k = j
    cases j with
    | zero => rfl
    | succ j => rfl
  rw [hshift]
  change Z_to_bv 64 (((n >>> (4 * k)) &&& 15 : Nat) : Int) = _
  have hm (a : Nat) : a &&& 15 = a % 16 := by
    exact Nat.and_two_pow_sub_one_eq_mod a 4
  rw [hm, Nat.shiftRight_eq_div_pow]
  have hp : (16 : Nat) ^ k = 2 ^ (4 * k) := by rw [Nat.pow_mul]
  rw [← hp]
  rfl

theorem hdr8_nth (n i : Nat) (d : byte) (Hi : i < 8) :
    (hdr8 n).getD i d = hex_digit (nib n (7 - i)) := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | i + 8 => omega

/-- Collapse the mmap-grant post-state to a `mkst` over the zero-filled
overlay. This is `CatExec.adv_set` with the effect's zero range folded in. -/
theorem adv_apply (regs : bvmap 5 word) (pc : word) (sv : Option word)
    (mem rom : word → Option byte) (a n : word) :
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := sv, ms_resv := none, ms_fcsr := Z_to_bv 32 0,
        ms_mem := mem, ms_rom := rom }
      (mkEffect a [] [(a, n)])) =
      mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom :=
  adv_mmap_grant regs pc sv mem rom a n

/-- The same collapse for a read's delivered block: one write range and
no zero ranges. -/
theorem adv_write (regs : bvmap 5 word) (pc : word) (sv : Option word)
    (mem rom : word → Option byte) (v buf : word) (bs : List byte) :
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := sv, ms_resv := none, ms_fcsr := Z_to_bv 32 0,
        ms_mem := mem, ms_rom := rom }
      (mkEffect v [(buf, bs)] [])) =
      mkst (regupd regs 10 v) (v_addi pc 4) (write_to_mem mem buf bs) rom :=
  LinuxProcessSemantics.Common.StreamExec.adv_apply_write regs pc sv mem rom v buf bs

end LinuxProcessSemantics.Examples.arena_tee_ns.arena_tee_ns_defs
