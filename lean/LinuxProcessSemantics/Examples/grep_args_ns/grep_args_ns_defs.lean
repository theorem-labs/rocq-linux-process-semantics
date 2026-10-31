import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.WallSim
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.MuslStrlen
import LinuxProcessSemantics.Common.StreamSim
import LinuxProcessSemantics.Common.StoreOk
import LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_code
import LinuxProcessSemantics.Examples.grep_args_ns.SourceMemImage
import LinuxProcessSemantics.Examples.grep_args_ns.TargetMemImage

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Mirrors `theories/Examples/grep_args_ns/grep_args_ns_defs.v` at the baseline above;
this proof-side file shares the observable-behavior specification (`grep_bufs`
and friends) and arithmetic/image facts so that the two binaries' stepping
files compile separately. See `Proof.v` for the shape of the whole proof.
Rocq `Z` is `Int`, `nat` is `Nat`, `firstn`/`skipn` are `List.take`/`List.drop`,
and Section variables become explicit arguments or `variable`s. Rocq `Forall`
is expressed by membership-indexed universal quantification, as in Common.
`of_nat_word_to_nat` is reused from `Common.StoreOk` rather than redeclared.
-/

namespace LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_defs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.StoreOk
open LinuxProcessSemantics.Examples.grep_args_ns.SourceMemImage
open LinuxProcessSemantics.Examples.grep_args_ns.TargetMemImage
open LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_code

/- The shared observable-behavior spec.
`byte_at` (byte k of string s laid out as s then a NUL) lives in CatExec. -/

/-- Do the bytes of `p` occur in `hay` starting at index `k`? -/
def prefix_eqb (p hay : List byte) (k : Nat) : Bool :=
  match p with
  | [] => true
  | b :: p' => bv_eqb (byte_at hay k) b && prefix_eqb p' hay (k + 1)

/-- Scan positions k, k+1, ... (fuel-bounded). -/
def scan_from (hay pat : List byte) (k fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 => prefix_eqb pat hay k || scan_from hay pat (k + 1) f

/-- `pat` occurs as a substring of `hay`. -/
def contains_b (hay pat : List byte) : Bool :=
  if pat.length = 0 then true
  else if hay.length < pat.length then false
  else scan_from hay pat 0 (Nat.succ (hay.length - pat.length))

/-- A matching argument contributes itself and a newline. Both binaries skip
an empty argument's zero-length write, so it contributes only the newline. -/
def arg_bufs (pat a : List byte) : List (List byte) :=
  if contains_b a pat then
    match a with
    | [] => [[Z_to_bv 8 10]]
    | _ => [a, [Z_to_bv 8 10]]
  else []

def grep_bufs (pat : List byte) (args : List (List byte)) : List (List byte) :=
  args.flatMap (arg_bufs pat)

/-- The matching argument is written whole; `Run.valid_argv` caps it at
131071 bytes, one below `rw_bytes_max`. The other buffer is a one-byte newline,
so these bounds discharge `CatSim.buf_modeled` for the contributed buffers. -/
theorem arg_bufs_modeled (pat a : List byte)
    (Ha : (a.length : Int) ≤ 131071) : bufs_modeled (arg_bufs pat a) := by
  unfold arg_bufs
  split
  · have Hnl : buf_modeled [Z_to_bv 8 10] := by
      unfold buf_modeled rw_bytes_max
      decide
    cases a with
    | nil =>
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst b
      exact Hnl
    | cons b a' =>
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · unfold buf_modeled rw_bytes_max
        omega
      · exact Hnl
  · intro b hb
    exact False.elim (List.not_mem_nil hb)

theorem grep_bufs_modeled (pat : List byte) (args : List (List byte))
    (Hargs : ∀ a ∈ args, (a.length : Int) ≤ 131071) :
    bufs_modeled (grep_bufs pat args) := by
  intro b hb
  obtain ⟨a, ha, hab⟩ := List.mem_flatMap.mp hb
  exact arg_bufs_modeled pat a (Hargs a ha) b hab

/-- `Run.valid_argv`'s per-argument bound survives dropping the leading
program name and pattern. -/
theorem Forall_skipn_argv (P : List byte → Prop) (n : Nat)
    (args : List (List byte)) (H : ∀ a ∈ args, P a) :
    ∀ a ∈ args.drop n, P a := by
  intro a ha
  exact H a (List.mem_of_mem_drop ha)

/- Shared small facts.
`nth_lt_byte_at`, `byte_at_len`, `byte_at_nz`, `byte_at_bound`, and the
`valid_argv` length/string facts live in CatExec.

Musl's word-at-a-time zero-byte test, the `bytes_le_to_Z` bridge, and the
readability of a NUL-straddling eight-byte load live in Common.MuslStrlen:
`HZ.Tz_nozero` / `HZ.Tz_haszero` prove the has-zero test exact;
`v_haszero`, `zb_of_bytes`, and `bytes_le_to_Z_range` bridge words and bytes;
`bsb_len_lower`, `total_arg_bytes_firstn_S`, `read_word_stack`, and
`argv_word_readable` justify reads up to seven bytes past an argv NUL.
That argument does not transfer to a heap/brk/mmap buffer; see that file.

The Rocq `of_nat_word_to_nat` declaration is Common.StoreOk.of_nat_word_to_nat.
-/

theorem v_slli3_nat (i : Nat) (Hi : (i : Int) ≤ 1024) :
    v_slli (nat_to_word i) 3 = Z_to_bv 64 (8 * (i : Int)) := by
  apply bv_eq_of_unsigned
  have hu := u_ntw i (by omega)
  rw [v_slli_3 _ (by rw [hu]; omega), hu, u_Z2bv _ (by omega) (by omega)]

theorem word_to_nat_ntw (n : Nat) (Hn : (n : Int) < 2 ^ 64) :
    word_to_nat (nat_to_word n) = n := by
  have hu := u_ntw n Hn
  rw [← of_nat_word_to_nat] at hu
  omega

/-- `v_add` variants of the `nat_to_word` merge laws: wrapping addition
agrees with word addition, but rewriting keys on the head symbol. -/
theorem v_add_ntw_merge (a : word) (m k : Nat) :
    v_add (a + nat_to_word m) (nat_to_word k) = a + nat_to_word (m + k) := by
  rw [LinuxProcessSemantics.Common.StepTac.v_add_comm, BitVec.add_comm]
  exact nat_to_word_add_merge a m k

theorem v_add_ntw (m k : Nat) :
    v_add (nat_to_word m) (nat_to_word k) = nat_to_word (m + k) := by
  rw [LinuxProcessSemantics.Common.StepTac.v_add_comm, BitVec.add_comm]
  exact nat_to_word_merge m k

/- `c_eq_0_of_u` lives in Common.PropExec. -/

/-- Byte comparison commutes with the zero-extension used by byte loads. -/
theorem bv_eqb_zext (b c : byte) :
    bv_eqb (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (bv_unsigned c)) =
      bv_eqb b c := by
  rw [Bool.eq_iff_iff]
  simp only [bv_eqb, beq_iff_eq]
  constructor
  · intro h
    apply bv_eq_of_unsigned
    have hu := congrArg bv_unsigned h
    rw [u_zext8, u_zext8] at hu
    exact hu
  · intro h
    subst c
    rfl

/- Step chaining and sp-independent helpers.
`norm_pc`, `stepi`, `stepiv`, `stepj`, `sp_norm`, `wlit`, and `wlits` live
in Common.StepTac. The negative-immediate instances `v_addi_m16` and
`v_addi_m64` live there in canonical `Z_to_bv 64 (...)` form.
The value-precise store with pre-normalized address, `step_sd_at`, lives
in Common.SeqExec. -/

/-- A store above the read-only segments passes read-only avoidance; the
rw data segment is exempt. After the `-z separate-code` relink the three
read-only windows are r-- headers `[0x10000, 0x11000)`, r-x text
`[0x11000, 0x12000)`, and r-- rodata `[0x12000, 0x13000)`, so the first
writable address is 0x13000. -/
theorem source_avoids_ro (a : word) (n : Int) (Ha : 0x13000 ≤ bv_unsigned a) :
    range_avoids_ro_segs source_segs (bv_unsigned a) n = true := by
  exact range_avoids_ro_above source_segs 0x13000 (bv_unsigned a) n (by decide) Ha

/-- The source rw segment covers `[0x13000, 0x14000)`, with a snapshot
byte at each address (the hex zero-fills bss). Thus a data/bss store needs
no prior write to define `wview`. Stack targets instead use the RLIMIT_STACK
window through `solve_store_ok`. -/
theorem source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true := by
  apply wseg_ok_backed source_segs SourceMemImage_segment_003 _ _
    [SourceMemImage_seg_bytes_003_chars]
  · simp only [source_segs, Source.loaded_segments, SourceMemImage_loaded_segments,
      wseg_cover]
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_left (by decide), ite_eq_left (by decide)]
  · decide
  · change [SourceMemImage_seg_bytes_003] = _
    rw [SourceMemImage_seg_bytes_003_chars_eq]
    rfl
  · intro cs h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst cs
    exact SourceMemImage_seg_bytes_003_ascii
  · intro cs h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst cs
    exact SourceMemImage_seg_bytes_003_hex
  · intro cs h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst cs
    simp only [SourceMemImage_seg_bytes_003_chars, List.length_replicate]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      SourceMemImage_seg_bytes_003_chars, List.length_replicate]
    decide
  · decide

theorem source_store_ok (m : word → Option byte) (a : word) (n : Nat)
    (Hlo : 0x13000 ≤ bv_unsigned a)
    (Hhi : bv_unsigned a + (n : Int) ≤ 0x14000) :
    store_ok source_segs m a n = true :=
  store_ok_window source_segs m 0x13000 a 4096 n 0x13000 0x14000
    rfl rfl (by decide) source_data_wseg Hlo Hhi

theorem target_avoids_ro (a : word) (n : Int) (Ha : 0x1002000 ≤ bv_unsigned a) :
    range_avoids_ro_segs target_segs (bv_unsigned a) n = true := by
  apply range_avoids_two
  · change decide (bv_unsigned a < 0x1001000) = false
    exact decide_eq_false (by omega)
  · change decide (bv_unsigned a < 0x1002000) = false
    exact decide_eq_false (by omega)

/- `total_arg_bytes_firstn_S`, `bsb_len_lower`, `bsb_word_k`, and
`read_word_stack` live in Common.MuslStrlen. -/

end LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_defs
