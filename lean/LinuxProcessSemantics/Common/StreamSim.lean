import LinuxProcessSemantics.LinuxProcessSem.Run
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
import LinuxProcessSemantics.LinuxProcessSem.StreamLaws
import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.WallSim
import LinuxProcessSemantics.Common.SimInv

/-! # Common.StreamSim — the read node of the streamcat library

Ported from `theories/Common/StreamSim.v` at
2cde689f94c086b868999970834b76a25616b94a: the part of it `cat1024_ns`'s
`Proof.v` reaches (`Print All Dependencies` of its
`strong_universal`, ticket E-proof-library), with the Rocq statements.
`m_fs_with_stdin` is outside that part: it is ported for `arena_tee_ns`'s
proof.

The library serves binaries that loop `n = read(0, buf, cnt); if n <= 0
exit(0); write(1, buf, n)` over one `cnt`-byte buffer.  The first part is
the per-read half: which arm answers the read number, the loop's model
invariant `M_loop`, the writable-segment range check `wseg_ok` (decided
once per image, then good for EVERY machine state), and the fd-0 read
node — the two outcomes a read with a writable destination admits,
end-of-input and a nonempty prefix of the remaining input, and the
one-step inversion `sstep_read_inv` that says nothing else happens.  The
second is the loop's trace set (`chunks`, `stream_traces`) and its phase
relations (`to_wr`, `to_rd`), with Rocq's generated induction principles
`chunks_ind`, `to_wr_ind` and `to_rd_ind` (stated as theorems here, since
Lean generates no non-dependent `_ind`), star admissibility and exhaustiveness
(`stream_star_admits`, `star_loop_only`); the third is the no-error
invariant `sinv` and the whole-run statements down to
`stream_omni_strong_equiv`.

Everything else in the Rocq file is unported; cat1024_ns reaches none of
it.  Among it: `in_arg1_sys_input`, `in_arg2_sys_input`,
`m_fds_with_stdin`, `M_loop_fd1chan`, `chunks_app`,
`chunks_split`, `chunks_single_inv`, `msteps_to_wr`, `to_wr_star`,
`star_sinv`, `to_rd_no_error`, `stream_no_error`, `stream_omni_cosafe` and
`stream_strong_equiv`.  Rocq's `StreamSim.msteps_to_wr` has the same closed
statement as the ported `SymTac.msteps_to_wr`.

One theorem is Lean-only: `read0_check_range_fails`, the failing side of
`read0_check_eof`'s range premise (its docstring says what it pins).

Representation divergences, spelled Lean's way:
- Rocq `fst`/`snd` are `.1`/`.2`, `Z.of_nat (length bs)` is the cast
  `(bs.length : Int)`, `flat_map` is `List.flatMap`, `(_ <= _)%nat` is
  `Nat`'s `≤`, and `wseg_ok`'s `Z.to_N`/`Z.of_N` offset is `Int.toNat`
  over the `Nat → Int` cast, as in `RiscvSemantics.wview`.
- Rocq's combined `(0 < bv_unsigned cnt <= rw_bytes_max)%Z` is the
  conjunction `0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max`.
- Rocq's input stream is a `CoInductive` (so an input may be infinite)
  and its proofs `destruct (m_stdin model)`; Lean's `InputStream` is a structure the checker
  inspects through `InputStream.uncons`, so the proofs go through
  `StreamLaws.uncons_eq_none_iff`/`uncons_eq_some_iff` instead, and
  `eof_tail`'s Rocq `match s with IEof => … | ICons _ _ => …` is a match on
  `s.uncons`.  The statements, `m_stdin model = IEof` included, are
  unchanged.
- Rocq Section variables become explicit leading arguments, in the order
  `Section Loop` closes them: `segs LH` for `lh_next`, `WrPend`, `to_wr`;
  `segs LH cnt` for `ReadPend`, `to_rd`, `sinv`; and the hypotheses `Hcnt`,
  `H_LH` where the Rocq proof uses them (so `sinv_no_error`, whose Rocq
  proof never uses `H_LH`, does not take it).  Rocq's `N` entry pc is
  `Nat`. -/

namespace LinuxProcessSemantics.Common.StreamSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite

/-! ## Syscall-input decoding -/

/-- Which arm answers this number, on the SPEC side.  `syscall_spec` is
`dispatch spec_table`, so fixing the number settles the table lookup by
conversion -- the same one-line argument Rocq's
`Checks.Sys.DispatchCompute` (unported) makes for `check_syscall`, made here so that this file needs only the
read checker rather than the module re-exporting every arm's.  See #580. -/
theorem syscall_spec_read (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (o : LinuxProcessSemantics.LinuxProcessSem.Monad.outcome SyscallEffect)
    (hno : bv_unsigned x8 = 63) :
    syscall_spec (sys_input segs ms x8) model o ↔
      read_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
        (sys_input segs ms x8) model o := by
  have hx : (sys_input segs ms x8).in_sysno = x8 := rfl
  unfold syscall_spec dispatch
  rw [hx, hno]
  exact Iff.rfl

theorem in_wmem_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_wmem = ms_writable_byte segs ms := rfl

/-- The masked exit code of exit(0). -/
theorem band0_255 : bv_and (Z_to_bv 64 0) (Z_to_bv 64 255) = Z_to_bv 64 0 := by decide

/-! ## Model helpers -/

theorem m_fs_with_stdin (s : InputStream) (m : Model) :
    m_fs (with_stdin s m) = m_fs m := rfl

theorem m_halted_with_stdin (s : InputStream) (m : Model) :
    m_halted (with_stdin s m) = m_halted m := rfl

theorem m_vm_lazy_with_stdin (s : InputStream) (m : Model) :
    m_vm_lazy (with_stdin s m) = m_vm_lazy m := rfl

/-- The model invariant maintained across loop iterations: fd 0/1 are the
stdin/stdout channels, the model is not halted, and nothing is lazily
mapped.  Nothing is said about WHAT is left in `m_stdin`: it shrinks as
the loop runs, and each lemma below relates it to the blocks delivered so
far.  End of input is the stream's own `IEof`, so there is no "not yet at
EOF" clause to maintain, and no byte-range clause either: the stream's
elements are `byte`. -/
def M_loop (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)) ∧
  fd_lookup (m_fds model) (Z_to_bv 64 1) = some (FdEntry.FdChannel (Z_to_bv 64 1)) ∧
  m_halted model = none ∧
  m_vm_lazy model = []

theorem init_M_loop (reserved : List (word × word)) (brk0 mb sp : word) (lim : Int)
    (inp : ProcInput) : M_loop (init_model reserved brk0 mb sp lim inp) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Consuming a read block preserves the invariant. -/
theorem M_loop_take (k : Nat) (model : Model) (h : M_loop model) :
    M_loop (with_stdin (stream_take (m_stdin model) k).2 model) :=
  h

/-! ## The writable-view range check

`wseg_ok` reduces the writable-view range check to a boolean over the
static segment image.  `ms_writable_byte` consults the writable overlay
FIRST and falls back to the segment bytes; an overlay entry can only
override a defined segment byte with another defined byte, so if the
segment view alone is defined on the whole range the writable view is
too, for EVERY machine state.  The segment lookup is the interpreter's
`Int`-comparison `find_segment`. -/

def wseg_ok (segs : List Segment) (a : word) (n : Nat) : Bool :=
  match n with
  | 0 => true
  | n' + 1 =>
    match find_segment segs (bv_unsigned a) 1 with
    | some seg =>
      (seg_writable seg
        && (match segment_byte_at seg.seg_bytes (Int.toNat (bv_unsigned a - (seg.seg_base : Int))) with
            | some _ => true
            | none => false)
        && wseg_ok segs (a + 1) n')
    | none => false

theorem wseg_ok_read_aux (segs : List Segment) (n : Nat) (a : word) (ms : machine_state)
    (h : wseg_ok segs a n = true) :
    ∃ w, read_bytes_aux (ms_writable_byte segs ms) a n = some w := by
  induction n generalizing a with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    simp only [wseg_ok] at h
    cases hseg : find_segment segs (bv_unsigned a) 1 with
    | none =>
      simp only [hseg] at h
      cases h
    | some seg =>
      simp only [hseg, Bool.and_eq_true] at h
      obtain ⟨⟨hwr, hbyte⟩, hrec⟩ := h
      cases hb : segment_byte_at seg.seg_bytes (Int.toNat (bv_unsigned a - (seg.seg_base : Int))) with
      | none =>
        simp only [hb] at hbyte
        cases hbyte
      | some b =>
        obtain ⟨w, hw⟩ := ih (a + 1) hrec
        have hdef : ∃ b0, ms_writable_byte segs ms a = some b0 := by
          unfold ms_writable_byte wview
          cases ms.ms_mem a with
          | some b' => exact ⟨b', rfl⟩
          | none =>
            simp only [hseg, hwr, ↓reduceIte, hb]
            exact ⟨b, rfl⟩
        obtain ⟨b0, hb0⟩ := hdef
        simp only [read_bytes_aux, hb0, hw]
        exact ⟨_, rfl⟩

theorem wseg_ok_wdef (segs : List Segment) (a len : word) (ms : machine_state)
    (h : wseg_ok segs a (word_to_nat len) = true) :
    ∃ w, read_bytes_map (ms_writable_byte segs ms) a len = some w := by
  rw [read_bytes_map_eq]
  exact wseg_ok_read_aux segs _ a ms h

/-! ## The fd-0 read node

Channel-read facts for fd 0 and count `cnt`, through the verified checker,
parameterized over `cnt` so every consumer instantiates it rather than
re-proving the family.  `hcnt`'s lower half discharges `w_is0 cnt = false`
(a literal fact when `cnt` is a numeral, but not definitionally so for an
abstract `cnt`) and gives `read0_wmem1` its one writable byte, a statement
false at `cnt = 0`.  The upper half, `rw_bytes_max`, makes the clamp the
identity (`Uaccess.rw_count_clamp_of_rw`; a bound of `MAX_RW_COUNT` would
do for that), and it is what discharges `CatSim.buf_modeled` for the echo
write in the loop below.  The pending number is characterized as
`bv_unsigned x8 = 63`, the dispatcher's test.

Which bytes a read delivers is fixed by the model's remaining input
`m_stdin`: the two shapes are end of input (`m_stdin = IEof`, return 0)
and delivering the `bs.length`-byte prefix of the remaining input, which
then advances past it. -/

/-- At least one byte of the destination is writable — the one-byte test
whose failure `read_spec` answers with -EFAULT — whenever the whole
`cnt`-byte buffer is.  The fail-closed decline is the whole-need test,
discharged by `read0_wmem_need`. -/
theorem read0_wmem1 (cnt : word) (hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (w : List byte)
    (hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w) :
    ∃ w1, read_bytes_map (sys_input segs ms x8).in_wmem (ms_gpr ms 1)
      (Z_to_bv 64 1) = some w1 := by
  have h1 : bv_unsigned (Z_to_bv 64 1) = 1 := by decide
  rw [in_wmem_sys_input]
  exact ⟨_, read_bytes_map_prefix _ _ cnt (Z_to_bv 64 1) w (by omega) hw⟩

/-- The destination holds everything the stream could supply to this
count: `read_spec`'s partial-destination decline does not fire when the
whole `cnt` range is writable, since the bytes the source can supply are
at most the clamped count. -/
theorem read0_wmem_need (cnt : word) (hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (w : List byte) (s : InputStream)
    (hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w) :
    ∃ wn, read_bytes_map (sys_input segs ms x8).in_wmem (ms_gpr ms 1)
      (len_word (stream_take_z s (rw_count_clamp cnt)).1) = some wn := by
  rw [in_wmem_sys_input]
  refine ⟨_, read_bytes_map_prefix _ _ cnt _ w ?_ hw⟩
  rw [stream_take_z_eq]
  have hlen := stream_take_length (rw_count_clamp cnt).toNat s
  have hcl := rw_count_clamp_range cnt
  have hr := word_unsigned_range cnt
  have hle : rw_count_clamp cnt ≤ bv_unsigned cnt := by
    unfold rw_count_clamp
    exact Int.min_le_left _ _
  rw [len_word_unsigned _ (by unfold two_pow_64 MAX_RW_COUNT at *; omega)]
  omega

/-- End of input: return 0, no writes, no events, model unchanged.  Every
answer of this node takes the range passing `access_ok` as a premise
(`haok`): `vfs_read` (fs/read_write.c at v6.18.46) tests the range before
the fd's content is consulted, so end of input is answered only for a
range that passes.  `read0_check_range_fails` below is the failing side. -/
theorem read0_check_eof (cnt : word) (hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model) (w : List byte)
    (_hno : bv_unsigned x8 = 63)
    (hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (heof : m_stdin model = IEof)
    (hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (hg2 : ms_gpr ms 2 = cnt)
    (_hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (haok : access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true) :
    check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
      (mkEffect (Z_to_bv 64 0) [] []) model = CheckOk model [] := by
  have hcnt0 := w_is0_pos cnt hcnt.1
  have h32 : fd32 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide
  have hz : w_is0 (Z_to_bv 64 0) = true := by decide
  unfold check_read
  rw [hg0, h32, hfd, hg2, heof]
  simp only [hz, haok, hcnt0, uncons_eof, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact (check_ret_only_ok_iff _ _ _ _ _ _).2 ⟨rfl, rfl, rfl⟩

/-- Lean-only: the failing side of `read0_check_eof`'s premise `haok`.  At
a range `access_okb` refuses, whatever the input, end of input included,
the one effect accepted is the bare -EFAULT, with the model unchanged and
no event.  Every other effect is refused, the 0 that `read0_check_eof`
answers among them, so none is declined as `unmodeled` either. -/
theorem read0_check_range_fails (cnt : word)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (hg2 : ms_gpr ms 2 = cnt)
    (hbad : access_okb (ms_gpr ms 1) (bv_unsigned cnt) = false) :
    check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
        (mkEffect (errno_ret EFAULT) [] []) model = CheckOk model []
    ∧ ∀ eff, eff ≠ mkEffect (errno_ret EFAULT) [] [] →
      check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
        eff model = CheckReject := by
  have h32 : fd32 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide
  have hz : w_is0 (Z_to_bv 64 0) = true := by decide
  have harm : ∀ eff, check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
      (ms_gpr ms 2) eff model = check_ret_only eff (errno_ret EFAULT) model [] := by
    intro eff
    unfold check_read
    rw [hg0, h32, hfd, hg2]
    simp only [hz, hbad, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  refine ⟨?_, fun eff hne => ?_⟩
  · rw [harm]
    exact (check_ret_only_ok_iff _ _ _ _ _ _).2 ⟨rfl, rfl, rfl⟩
  · rw [harm]
    cases h : check_ret_only eff (errno_ret EFAULT) model [] with
    | CheckOk m1 evs1 => exact absurd ((check_ret_only_ok_iff _ _ _ _ _ _).1 h).1 hne
    | CheckReject => rfl
    | CheckUnmodeled => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- A nonempty prefix `bs` of the remaining input, at most `cnt` bytes,
written into the buffer with one `ReadEv 0 b` per byte.  The input cannot
have run out here, since a nonempty prefix was delivered. -/
theorem read0_check_bytes (cnt : word) (hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model) (w bs : List byte)
    (_hno : bv_unsigned x8 = 63)
    (hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (hg2 : ms_gpr ms 2 = cnt)
    (hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (haok : access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true)
    (hlo : 1 ≤ (bs.length : Int)) (hhi : (bs.length : Int) ≤ bv_unsigned cnt)
    (hpre : (stream_take (m_stdin model) bs.length).1 = bs) :
    check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
      (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] []) model
      = CheckOk (with_stdin (stream_take (m_stdin model) bs.length).2 model)
          (List.map (ReadEv (Z_to_bv 64 0)) bs) := by
  obtain ⟨w1, hw1⟩ := read0_wmem1 cnt hcnt segs ms x8 w hw
  obtain ⟨wn, hwn⟩ := read0_wmem_need cnt hcnt segs ms x8 w (m_stdin model) hw
  have hcnt0 := w_is0_pos cnt hcnt.1
  have h32 : fd32 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide
  have hz : w_is0 (Z_to_bv 64 0) = true := by decide
  -- the input cannot have run out: a nonempty prefix was delivered
  cases hu : (m_stdin model).uncons with
  | none =>
    rw [(uncons_eq_none_iff _).1 hu, stream_take_nil_of_eof] at hpre
    subst hpre
    have h0 : (([] : List byte).length : Int) = 0 := rfl
    omega
  | some p =>
    have hwf : read_bytes_map (sys_input segs ms x8).in_wmem (ms_gpr ms 1) cnt = some w := by
      rw [in_wmem_sys_input]
      exact hw
    have hr := word_unsigned_range cnt
    have hlek : bv_unsigned (len_word bs) ≤ bv_unsigned cnt := by
      rw [len_word_unsigned bs (by unfold two_pow_64 at hr ⊢; omega)]
      exact hhi
    rw [rw_count_clamp_of_rw cnt hcnt.2] at hwn
    unfold check_read
    rw [hg0, h32, hfd, hg2, hu]
    simp only [hz, haok, hcnt0, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      hw1, hwn, PropExec.bv_eqb_refl, hlo, rw_count_clamp_of_rw cnt hcnt.2, hhi, decide_true,
      (listN_eqb_eq _ _).2 hpre, wmem_ok_of_full _ _ _ _ _ hwf hlek, Bool.and_self]

theorem read0_ok_eof (cnt : word) (hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model) (w : List byte)
    (hno : bv_unsigned x8 = 63)
    (hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (heof : m_stdin model = IEof)
    (hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (hg2 : ms_gpr ms 2 = cnt)
    (hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (haok : access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true) :
    syscall_spec (sys_input segs ms x8) model
      (Ok (mkEffect (Z_to_bv 64 0) [] []) model []) :=
  (syscall_spec_read segs ms x8 model _ hno).2
    (check_read_sound_ok _ _ _ _ _ _ _ _
      (read0_check_eof cnt hcnt segs ms x8 model w hno hfd heof hg0 hg2 hw haok))

theorem read0_ok_bytes (cnt : word) (hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model) (w bs : List byte)
    (hno : bv_unsigned x8 = 63)
    (hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (hg2 : ms_gpr ms 2 = cnt)
    (hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (haok : access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true)
    (hlo : 1 ≤ (bs.length : Int)) (hhi : (bs.length : Int) ≤ bv_unsigned cnt)
    (hpre : (stream_take (m_stdin model) bs.length).1 = bs) :
    syscall_spec (sys_input segs ms x8) model
      (Ok (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] [])
        (with_stdin (stream_take (m_stdin model) bs.length).2 model)
        (List.map (ReadEv (Z_to_bv 64 0)) bs)) :=
  (syscall_spec_read segs ms x8 model _ hno).2
    (check_read_sound_ok _ _ _ _ _ _ _ _
      (read0_check_bytes cnt hcnt segs ms x8 model w bs hno hfd hg0 hg2 hw haok hlo hhi hpre))

/-- Every admissible outcome of the read IS one of the two shapes, and
WHICH one is decided by the remaining input, not by the environment. -/
theorem read0_ok_inv (cnt : word) (hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model) (buf : word)
    (w : List byte) (eff : SyscallEffect) (model' : Model) (evs : List event)
    (hno : bv_unsigned x8 = 63)
    (hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (hg1 : ms_gpr ms 1 = buf) (hg2 : ms_gpr ms 2 = cnt)
    (hw : read_bytes_map (ms_writable_byte segs ms) buf cnt = some w)
    (haok : access_okb buf (bv_unsigned cnt) = true)
    (hspec : syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) :
    (m_stdin model = IEof ∧ eff = mkEffect (Z_to_bv 64 0) [] [] ∧
      model' = model ∧ evs = []) ∨
    (∃ bs : List byte,
      1 ≤ (bs.length : Int) ∧
      (bs.length : Int) ≤ bv_unsigned cnt ∧
      (stream_take (m_stdin model) bs.length).1 = bs ∧
      eff = mkEffect (len_word bs) [(buf, bs)] [] ∧
      model' = with_stdin (stream_take (m_stdin model) bs.length).2 model ∧
      evs = List.map (ReadEv (Z_to_bv 64 0)) bs) := by
  obtain ⟨w1, hw1⟩ := read0_wmem1 cnt hcnt segs ms x8 w (by rw [hg1]; exact hw)
  rw [hg1] at hw1
  obtain ⟨wn, hwn⟩ := read0_wmem_need cnt hcnt segs ms x8 w (m_stdin model)
    (by rw [hg1]; exact hw)
  rw [hg1] at hwn
  have hcnt0 := w_is0_pos cnt hcnt.1
  have h32 : fd32 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide
  have hz : w_is0 (Z_to_bv 64 0) = true := by decide
  have hck := check_read_complete_ok _ _ _ _ _ _ _ _
    ((syscall_spec_read segs ms x8 model _ hno).1 hspec)
  unfold check_read at hck
  rw [hg0, h32, hfd, hg1, hg2] at hck
  simp only [hz, haok, hcnt0, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hck
  cases hu : (m_stdin model).uncons with
  | none =>
    -- the input has run out
    rw [hu] at hck
    obtain ⟨he, hm, hev⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).1 hck
    exact Or.inl ⟨(uncons_eq_none_iff _).1 hu, he, hm, hev⟩
  | some p =>
    -- bytes delivered from the head of the remaining input
    rw [hu] at hck
    simp only [hw1, hwn] at hck
    obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
    cases ws with
    | nil => cases hck
    | cons wr ws =>
    cases ws with
    | cons _ _ => cases hck
    | nil =>
    obtain ⟨a, bs⟩ := wr
    cases zs with
    | cons _ _ => cases hck
    | nil =>
    cases us with
    | cons _ _ => cases hck
    | nil =>
    cases cs with
    | cons _ _ => cases hck
    | nil =>
    cases copyins with
    | cons _ _ => cases hck
    | nil =>
    dsimp only at hck
    split at hck
    · rename_i hgr
      cases hck
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hgr
      obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩, _⟩ := hgr
      have ha' := (bv_eqb_eq a buf).1 ha
      have hb' := (bv_eqb_eq ret (len_word bs)).1 hb
      subst ha' hb'
      rw [rw_count_clamp_of_rw cnt hcnt.2] at hd
      exact Or.inr ⟨bs, hc, hd, (listN_eqb_eq _ _).1 he, rfl, rfl, rfl⟩
    · cases hck

/-- The read never takes the error transition (the destination is
writable). -/
theorem read0_no_unmodeled (cnt : word)
    (hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model) (w : List byte)
    (hno : bv_unsigned x8 = 63)
    (hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (hg2 : ms_gpr ms 2 = cnt)
    (hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (haok : access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true) :
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled := by
  intro hspec
  obtain ⟨w1, hw1⟩ := read0_wmem1 cnt hcnt segs ms x8 w hw
  obtain ⟨wn, hwn⟩ := read0_wmem_need cnt hcnt segs ms x8 w (m_stdin model) hw
  have hcnt0 := w_is0_pos cnt hcnt.1
  have h32 : fd32 (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide
  have hz : w_is0 (Z_to_bv 64 0) = true := by decide
  have hck := check_read_complete_unmodeled _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []) _
    ((syscall_spec_read segs ms x8 model _ hno).1 hspec)
  unfold check_read at hck
  rw [hg0, h32, hfd, hg2] at hck
  simp only [hz, haok, hcnt0, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hck
  cases hu : (m_stdin model).uncons with
  | none =>
    rw [hu] at hck
    exact check_ret_only_no_unmodeled _ _ _ _ hck
  | some p =>
    rw [hu] at hck
    simp only [hw1, hwn] at hck
    cases hck

/-! ## One-step inversion at a read-pending config -/

theorem sstep_read_inv (cnt : word) (hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (model : Model) (buf x8 : word) (w : List byte)
    (evs : List event) (st : step_to)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (hsvc : ms.ms_svc_pending = some x8) (hno : bv_unsigned x8 = 63)
    (hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (hg1 : ms_gpr ms 1 = buf) (hg2 : ms_gpr ms 2 = cnt)
    (hw : read_bytes_map (ms_writable_byte segs ms) buf cnt = some w)
    (haok : access_okb buf (bv_unsigned cnt) = true)
    (hss : sstep segs (config.mkCfg ms model) evs st) :
    (m_stdin model = IEof ∧ evs = [] ∧
      st = SNext (config.mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model)) ∨
    (∃ bs : List byte,
      1 ≤ (bs.length : Int) ∧
      (bs.length : Int) ≤ bv_unsigned cnt ∧
      (stream_take (m_stdin model) bs.length).1 = bs ∧
      evs = List.map (ReadEv (Z_to_bv 64 0)) bs ∧
      st = SNext (config.mkCfg
        (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] [])))
        (with_stdin (stream_take (m_stdin model) bs.length).2 model))) := by
  have hlazy' : ∀ s, m_vm_lazy (with_stdin s model) = [] := fun s =>
    (m_vm_lazy_with_stdin s model).trans hlazy
  cases hss with
  | sstep_instr _ _ _ _ _ hv _ => rw [hsvc] at hv; cases hv
  | sstep_instr_fault _ _ _ hv _ => rw [hsvc] at hv; cases hv
  | sstep_instr_unmodeled _ _ _ hv _ => rw [hsvc] at hv; cases hv
  | sstep_syscall _ _ x8' eff m' m'' evs' _ hv hspec _ hmat =>
    rw [hsvc] at hv
    cases hv
    rcases read0_ok_inv cnt hcnt segs ms x8 model buf w eff m' _ hno hfd hg0 hg1 hg2 hw haok
        hspec with ⟨hs, heff, hm, hevs⟩ | ⟨bs, hlo, hhi, hpre, heff, hm, hevs⟩
    · subst heff hm hevs
      rw [materialize_model_accesses_no_lazy _ _ hlazy] at hmat
      cases hmat
      exact Or.inl ⟨hs, rfl, rfl⟩
    · subst heff hm hevs
      rw [materialize_model_accesses_no_lazy _ _ (hlazy' _)] at hmat
      cases hmat
      exact Or.inr ⟨bs, hlo, hhi, hpre, rfl, rfl⟩
  | sstep_syscall_materialization_fault _ _ x8' eff m' evs' _ hv hspec _ hmat =>
    -- this loop has no lazy maps
    rw [hsvc] at hv
    cases hv
    rcases read0_ok_inv cnt hcnt segs ms x8 model buf w eff m' _ hno hfd hg0 hg1 hg2 hw haok
        hspec with ⟨_, _, hm, _⟩ | ⟨bs, _, _, _, _, hm, _⟩
    · subst hm
      rw [materialize_model_accesses_no_lazy _ _ hlazy] at hmat
      cases hmat
    · subst hm
      rw [materialize_model_accesses_no_lazy _ _ (hlazy' _)] at hmat
      cases hmat
  | sstep_exit _ _ x8' eff m' evs' code _ hv hspec hh' _ =>
    -- the read leaves the model un-halted
    rw [hsvc] at hv
    cases hv
    rcases read0_ok_inv cnt hcnt segs ms x8 model buf w eff m' _ hno hfd hg0 hg1 hg2 hw haok
        hspec with ⟨_, _, hm, _⟩ | ⟨bs, _, _, _, _, hm, _⟩
    · subst hm
      rw [hh] at hh'
      cases hh'
    · subst hm
      rw [m_halted_with_stdin, hh] at hh'
      cases hh'
  | sstep_killed _ _ x8' eff m' evs' sig _ hv hspec hk =>
    -- the read leaves the model unkilled, as it leaves it un-halted --
    -- `State.m_killed_of_m_halted_none` on the pre-model
    rw [hsvc] at hv
    cases hv
    rcases read0_ok_inv cnt hcnt segs ms x8 model buf w eff m' _ hno hfd hg0 hg1 hg2 hw haok
        hspec with ⟨_, _, hm, _⟩ | ⟨bs, _, _, _, _, hm, _⟩
    · subst hm
      rw [m_killed_of_m_halted_none _ hh] at hk
      cases hk
    · subst hm
      rw [m_killed_of_m_halted_none _ ((m_halted_with_stdin _ model).trans hh)] at hk
      cases hk
  | sstep_syscall_unmodeled _ _ x8' _ hv hspec =>
    rw [hsvc] at hv
    cases hv
    exact absurd hspec
      (read0_no_unmodeled cnt hcnt segs ms x8 model w hno hfd hg0 hg2 (by rw [hg1]; exact hw)
        (by rw [hg1]; exact haok))

open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.WallSim

/-! ## The trace-set characterization -/

/-- How a run CHUNKS its input: `chunks cnt s blocks s'` says the loop can
consume `s` as the successive read blocks `blocks`, leaving `s'` unread.
Each block is a nonempty prefix of at most `cnt` bytes of what remains —
WHICH bytes is fixed by the input, only how many is the read's (short-read)
nondeterminism. -/
inductive chunks (cnt : word) : InputStream → List (List byte) → InputStream → Prop
  | chunks_nil : ∀ s, chunks cnt s [] s
  | chunks_cons : ∀ s bs blocks s'',
      1 ≤ (bs.length : Int) →
      (bs.length : Int) ≤ bv_unsigned cnt →
      (stream_take s bs.length).1 = bs →
      chunks cnt (stream_take s bs.length).2 blocks s'' →
      chunks cnt s (bs :: blocks) s''

/-- Rocq's generated induction principle for `chunks`.  Lean generates no
non-dependent `_ind`: `chunks.rec`, and the `recOn`/`casesOn` built on it,
take a motive over the derivation, so it is stated here with the Rocq
statement. -/
theorem chunks_ind (cnt : word) (P : InputStream → List (List byte) → InputStream → Prop)
    (f : ∀ s, P s [] s)
    (f0 : ∀ s bs blocks s'',
      1 ≤ (bs.length : Int) →
      (bs.length : Int) ≤ bv_unsigned cnt →
      (stream_take s bs.length).1 = bs →
      chunks cnt (stream_take s bs.length).2 blocks s'' →
      P (stream_take s bs.length).2 blocks s'' →
      P s (bs :: blocks) s'') :
    ∀ i l i0, chunks cnt i l i0 → P i l i0 := by
  intro i l i0 h
  induction h with
  | chunks_nil s => exact f s
  | chunks_cons s bs blocks s'' h1 h2 h3 h ih => exact f0 s bs blocks s'' h1 h2 h3 h ih

/-- One loop iteration's events, reading on channel `rch`: the block is
read byte-by-byte and echoed byte-by-byte to stdout.  The echo write may
take several (possibly short) channel writes, but the put-style retry loop
always delivers the WHOLE block, so — chunking-independently — an
iteration's write contribution is all of `bs`. -/
def iter_ev_ch (rch : word) (bs : List byte) : List event :=
  List.map (ReadEv rch) bs ++ List.map (WriteEv (Z_to_bv 64 1)) bs

/-- One loop iteration's events, reading on stdin — the only `FdChannel`
a read can name (`ReadWrite.read_spec` answers -EBADF on every other
channel; a connected socket, a separate fd kind, reads on its own). -/
def iter_ev (bs : List byte) : List event :=
  iter_ev_ch (Z_to_bv 64 0) bs

/-- What follows the last block: the loop exits 0 exactly when the input
has run out.  While input remains, the run has not stopped — the trace so
far is just a prefix. -/
def eof_tail (s : InputStream) (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) :
    List event :=
  match s.uncons with
  | none => [ExitEv (Z_to_bv 64 0) fs]
  | some _ => []

/-- The trace set of an echo loop with a `cnt`-byte buffer reading channel
`rch` on input `s`: the prefixes of
`flat_map (iter_ev_ch rch) blocks ++ eof_tail s' fs` over all chunkings of
`s` into read blocks. -/
def stream_traces_ch (rch cnt : word) (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs)
    (s : InputStream) (tr : List event) : Prop :=
  ∃ blocks s', chunks cnt s blocks s' ∧
    is_prefix tr (List.flatMap (iter_ev_ch rch) blocks ++ eof_tail s' fs)

/-- The full observable trace set of a streamcat binary with a `cnt`-byte
buffer on input `s`.  Reads name channel 0 because the loop reads fd 0 and
`M_loop` binds fd 0 to `FdChannel 0`; `ReadWrite.read_spec` answers -EBADF
on every other `FdChannel`.  The
exit event appears only in the
chunkings that reached the end of the input; an INFINITE input contributes
only the (unbounded, but each finite) block prefixes, which is exactly
right — such a run never exits. -/
def stream_traces (cnt : word) (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs)
    (s : InputStream) (tr : List event) : Prop :=
  stream_traces_ch (Z_to_bv 64 0) cnt fs s tr

theorem stream_traces_ch_prefix_closed (rch cnt : word)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (s : InputStream)
    (tr tr' : List event) (H : stream_traces_ch rch cnt fs s tr) (Hp' : is_prefix tr' tr) :
    stream_traces_ch rch cnt fs s tr' := by
  obtain ⟨blocks, s', HC, Hp⟩ := H
  exact ⟨blocks, s', HC, is_prefix_trans _ _ _ Hp' Hp⟩

theorem stream_traces_prefix_closed (cnt : word)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (s : InputStream)
    (tr tr' : List event) (H : stream_traces cnt fs s tr) (Hp' : is_prefix tr' tr) :
    stream_traces cnt fs s tr' :=
  stream_traces_ch_prefix_closed (Z_to_bv 64 0) cnt fs s tr tr' H Hp'

/-! ## The generic loop theory, parameterized over the `cnt`-byte buffer size -/

/-- The state runs (deterministically) to some loop-head state. -/
def lh_next (segs : List Segment) (LH : machine_state → Prop) (ms : machine_state) : Prop :=
  ∃ ms', msteps segs ms ms' ∧ LH ms'

/-- A write-pending ecall state echoing block `bs`: the environment may
deliver any nonempty prefix per syscall, so the binary's put-style retry
loop must deliver ALL of `bs` — across one or more writes — and then run
back to a loop head.  That is exactly WallSim's write-all node with the
loop-head continuation. -/
def WrPend (segs : List Segment) (LH : machine_state → Prop) (bs : List byte)
    (ms : machine_state) : Prop :=
  1 ≤ bs.length ∧ to_wall segs (Z_to_bv 64 1) ms bs (lh_next segs LH)

/-- Straight line of instructions to a write-pending state for block `bs`. -/
inductive to_wr (segs : List Segment) (LH : machine_state → Prop) (bs : List byte) :
    machine_state → Prop
  | twr_here : ∀ ms, WrPend segs LH bs ms → to_wr segs LH bs ms
  | twr_step : ∀ ms ms',
      ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' →
      to_wr segs LH bs ms' → to_wr segs LH bs ms

/-- Rocq's generated induction principle for `to_wr`.  Lean generates no
non-dependent `_ind`: `to_wr.rec`, and the `recOn`/`casesOn` built on it,
take a motive over the derivation, so it is stated here with the Rocq
statement. -/
theorem to_wr_ind (segs : List Segment) (LH : machine_state → Prop) (bs : List byte)
    (P : machine_state → Prop)
    (f : ∀ ms, WrPend segs LH bs ms → P ms)
    (f0 : ∀ ms ms', ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      to_wr segs LH bs ms' → P ms' → P ms) :
    ∀ m, to_wr segs LH bs m → P m := by
  intro m h
  induction h with
  | twr_here ms hw => exact f ms hw
  | twr_step ms ms' hs hst h ih => exact f0 ms ms' hs hst h ih

/-- A read-pending ecall state (fd 0, count `cnt`, buffer a1 writable),
together with both continuations:
- when the input has run out, the run reaches an exit(0) ecall;
- on any admissible block, the run reaches the echo write and returns to a
  loop head.

The destination range passes `access_ok`, which `vfs_read`
(fs/read_write.c at v6.18.46) tests before it looks at the input.  The
test is `__access_ok` (include/asm-generic/access_ok.h at v6.18.46), whose
closing comparison is transcribed as `State.access_okb`: `buf + cnt ≤
TASK_SIZE` in unbounded arithmetic.  Ahead of that comparison it returns
true on a build without `CONFIG_MMU` or with
`CONFIG_ALTERNATE_USER_ADDRESS_SPACE`; the model is scoped to the other
builds and does not model that branch
(bugs/access-okb-early-return-unmodeled.md).  With
`CONFIG_RISCV_ISA_SUPM`, riscv64's own `access_ok`
(arch/riscv/include/asm/uaccess.h at v6.18.46) applies the test to the
untagged address.  `State.access_okb` does not untag; Rocq's comment on
`access_okb` (theories/LinuxProcessSem/State.v) argues why that is exact
for every process the model describes, under a closed-world assumption
that nothing here checks: that no tracer outside the model enables
pointer masking for it (bugs/access-okb-closed-world.md; the Lean copy
of the argument is in Checks/ProcessCreation.lean).  Being mapped is not
the range test — `read_bytes_map` walks the range in word arithmetic,
which wraps at 2^64.  A caller discharges this with the one inequality
`buf + cnt ≤ State.TASK_SIZE` (`Uaccess.access_okb_intro`).  A link-time
buffer meets it with room to spare; a stack buffer can meet it with none,
since riscv64's `STACK_TOP` is `DEFAULT_MAP_WINDOW`, which is
`UL(1) << (MMAP_VA_BITS - 1)` (arch/riscv/include/asm/processor.h at
v6.18.46), and `MMAP_VA_BITS` is 48 for a 64-bit task on Sv48 or Sv57
(arch/riscv/include/asm/pgtable.h at v6.18.46): on Sv48 the stack top is
2^47, the model's `TASK_SIZE`. -/
def ReadPend (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (ms : machine_state) : Prop :=
  ∃ buf x8,
    ms.ms_svc_pending = some x8 ∧
    bv_unsigned x8 = 63 ∧
    ms_gpr ms 0 = Z_to_bv 64 0 ∧
    ms_gpr ms 1 = buf ∧
    ms_gpr ms 2 = cnt ∧
    (∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w) ∧
    access_okb buf (bv_unsigned cnt) = true ∧
    to_exit segs (Z_to_bv 64 0) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) ∧
    (∀ bs, 1 ≤ (bs.length : Int) → (bs.length : Int) ≤ bv_unsigned cnt →
      to_wr segs LH bs
        (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] []))))

/-- A write phase IS a write-all tail derivation (the `to_wr` instruction
prefix becomes `twt_step`s in front of the `to_wall` node). -/
theorem to_wr_wall_tail (segs : List Segment) (LH : machine_state → Prop) (bs : List byte)
    (ms : machine_state) (H : to_wr segs LH bs ms) :
    to_wall_tail segs (Z_to_bv 64 1) ms bs (lh_next segs LH) := by
  induction H with
  | twr_here ms HWP =>
    obtain ⟨Hnb, Hw⟩ := HWP
    exact to_wall_tail.twt_more ms bs _ Hnb Hw
  | twr_step ms ms' Hsvc Hstep _ IH =>
    exact to_wall_tail.twt_step ms ms' bs _ Hsvc Hstep IH

/-- Straight line of instructions to a read-pending state. -/
inductive to_rd (segs : List Segment) (LH : machine_state → Prop) (cnt : word) :
    machine_state → Prop
  | trd_here : ∀ ms, ReadPend segs LH cnt ms → to_rd segs LH cnt ms
  | trd_step : ∀ ms ms',
      ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' →
      to_rd segs LH cnt ms' → to_rd segs LH cnt ms

/-- Rocq's generated induction principle for `to_rd`.  Lean generates no
non-dependent `_ind`: `to_rd.rec`, and the `recOn`/`casesOn` built on it,
take a motive over the derivation, so it is stated here with the Rocq
statement. -/
theorem to_rd_ind (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (P : machine_state → Prop)
    (f : ∀ ms, ReadPend segs LH cnt ms → P ms)
    (f0 : ∀ ms ms', ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      to_rd segs LH cnt ms' → P ms' → P ms) :
    ∀ m, to_rd segs LH cnt m → P m := by
  intro m h
  induction h with
  | trd_here ms hr => exact f ms hr
  | trd_step ms ms' hs hst h ih => exact f0 ms ms' hs hst h ih

theorem msteps_to_rd (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (ms ms' : machine_state) (H : msteps segs ms ms') (Hrd : to_rd segs LH cnt ms') :
    to_rd segs LH cnt ms := by
  induction H with
  | mst_refl _ => exact Hrd
  | mst_step ms0 ms1 _ Hsvc Hstep _ IH => exact to_rd.trd_step ms0 ms1 Hsvc Hstep (IH Hrd)

theorem lh_next_to_rd (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms) (ms : machine_state)
    (H : lh_next segs LH ms) : to_rd segs LH cnt ms := by
  obtain ⟨ms', Hm, HL⟩ := H
  exact msteps_to_rd segs LH cnt ms ms' Hm (H_LH ms' HL)

/-! ### Straight lines are event-free star runs -/

theorem to_rd_star (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (ms : machine_state) (model : Model)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hrd : to_rd segs LH cnt ms) :
    ∃ msR, ReadPend segs LH cnt msR ∧
      star segs (config.mkCfg ms model) [] (config.mkCfg msR model) := by
  induction Hrd with
  | trd_here ms HRP => exact ⟨ms, HRP, star.star_refl _⟩
  | trd_step ms ms' Hsvc Hstep _ IH =>
    obtain ⟨msR, HRP, Hstar⟩ := IH
    have hi : sstep segs (config.mkCfg ms model) [] (SNext (config.mkCfg ms' model)) :=
      sstep.sstep_instr ms model ms' model Hh Hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])
    exact ⟨msR, HRP, star.star_step _ [] _ [] _ hi Hstar⟩

/-! ### Admissibility: every stream trace is realized -/

theorem stream_star_admits (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (s : InputStream) (blocks : List (List byte)) (s' : InputStream)
    (HC : chunks cnt s blocks s') :
    ∀ (ms : machine_state) (model : Model), M_loop model → m_stdin model = s →
      to_rd segs LH cnt ms →
      ∃ c, star segs (config.mkCfg ms model)
        (List.flatMap iter_ev blocks ++ eof_tail s' (m_fs model)) c := by
  induction HC with
  | chunks_nil s =>
    -- no more blocks
    intro ms model HM Hst Hrd
    obtain ⟨Hfd0, _, Hh, Hlazy⟩ := HM
    cases hu : s.uncons with
    | none =>
      -- the input has run out: resolve the read as EOF, then exit(0)
      have hb : s.byte_at 0 = none := by
        unfold InputStream.uncons at hu
        cases hb : s.byte_at 0 with
        | none => rfl
        | some b =>
          rw [hb] at hu
          cases hu
      have hs : s = IEof := InputStream.eq_eof_of_head_none s hb
      subst hs
      obtain ⟨msR, ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hex, _⟩, Hstar0⟩ :=
        to_rd_star segs LH cnt ms model Hh Hlazy Hrd
      subst Hg1
      obtain ⟨c, Hstar2⟩ := to_exit_star_admits segs (Z_to_bv 64 0)
        (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0))) model Hh Hlazy Hex
      have hspec :=
        read0_ok_eof cnt Hcnt segs msR x8 model w Hno Hfd0 Hst Hg0 Hg2 Hw Haok
      have HssE := sstep.sstep_syscall msR model x8 (mkEffect (Z_to_bv 64 0) [] []) model model []
        Hh Hsvc hspec Hh (materialize_model_accesses_no_lazy model _ Hlazy)
      rw [apply_effect_no_write] at HssE
      have hall := star_trans _ _ _ _ _ _ Hstar0 (star.star_step _ _ _ _ _ HssE Hstar2)
      rw [band0_255] at hall
      exact ⟨c, hall⟩
    | some p =>
      -- input remains: the empty trace is a prefix of this run
      have ht : eof_tail s (m_fs model) = [] := by
        unfold eof_tail
        rw [hu]
      refine ⟨config.mkCfg ms model, ?_⟩
      rw [ht]
      exact star.star_refl _
  | chunks_cons s bs blocks s'' Hlo Hhi Hpre _ IH =>
    -- one more block: deliver it, echo ALL of it through the retry loop, loop
    intro ms model HM Hst Hrd
    have HM' : M_loop (with_stdin (stream_take s bs.length).2 model) := by
      rw [← Hst]
      exact M_loop_take bs.length model HM
    obtain ⟨Hfd0, _, Hh, Hlazy⟩ := HM
    obtain ⟨Hfd0', Hfd1', Hh', Hlazy'⟩ := HM'
    obtain ⟨msR, ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, _, Hbytes⟩, Hstar0⟩ :=
      to_rd_star segs LH cnt ms model Hh Hlazy Hrd
    subst Hg1
    have Hwr := Hbytes bs Hlo Hhi
    have hspec := read0_ok_bytes cnt Hcnt segs msR x8 model w bs Hno Hfd0 Hg0 Hg2 Hw Haok
      Hlo Hhi (by rw [Hst]; exact Hpre)
    rw [Hst] at hspec
    have HssR := sstep.sstep_syscall msR model x8
      (mkEffect (len_word bs) [(ms_gpr msR 1, bs)] [])
      (with_stdin (stream_take s bs.length).2 model) _ _
      Hh Hsvc hspec Hh' (materialize_model_accesses_no_lazy _ _ Hlazy')
    have Hfdc' : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
        (with_stdin (stream_take s bs.length).2 model) := fd1chan_fdchan _ Hfd1'
    have Hbmbs : buf_modeled bs := by
      unfold buf_modeled
      omega
    have Hcont : ∀ ms', lh_next segs LH ms' →
        ∃ c, star segs (config.mkCfg ms' (with_stdin (stream_take s bs.length).2 model))
          (List.flatMap iter_ev blocks ++
            eof_tail s'' (m_fs (with_stdin (stream_take s bs.length).2 model))) c :=
      fun ms' Hlh => IH ms' _ ⟨Hfd0', Hfd1', Hh', Hlazy'⟩ rfl
        (lh_next_to_rd segs LH cnt H_LH ms' Hlh)
    obtain ⟨c, Hstar1⟩ := to_wall_tail_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
      _ bs (lh_next segs LH) (to_wr_wall_tail segs LH bs _ Hwr) Hbmbs _ _ Hh' Hlazy' Hfdc' Hcont
    have hall := star_trans _ _ _ _ _ _ Hstar0 (star.star_step _ _ _ _ _ HssR Hstar1)
    refine ⟨c, ?_⟩
    rw [List.flatMap_cons]
    unfold iter_ev iter_ev_ch
    rw [List.append_assoc, List.append_assoc]
    exact hall

/-! ### Exhaustiveness: every run trace is a stream trace -/

theorem star_loop_only (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (c0 : config) (tr : List event) (c' : config) (Hstar : star segs c0 tr c') :
    ∀ (ms : machine_state) (model : Model), c0 = config.mkCfg ms model → M_loop model →
      (to_rd segs LH cnt ms →
        ∃ blocks s', chunks cnt (m_stdin model) blocks s' ∧
          is_prefix tr (List.flatMap iter_ev blocks ++ eof_tail s' (m_fs model))) ∧
      (∀ bs, 1 ≤ bs.length → buf_modeled bs →
        to_wall_tail segs (Z_to_bv 64 1) ms bs (lh_next segs LH) →
        ∃ blocks s', chunks cnt (m_stdin model) blocks s' ∧
          is_prefix tr (List.map (WriteEv (Z_to_bv 64 1)) bs ++
            (List.flatMap iter_ev blocks ++ eof_tail s' (m_fs model)))) := by
  induction Hstar with
  | star_refl c =>
    -- star_refl: the empty trace
    intro ms model _ _
    exact ⟨fun _ => ⟨[], m_stdin model, chunks.chunks_nil _, is_prefix_nil _⟩,
      fun _ _ _ _ => ⟨[], m_stdin model, chunks.chunks_nil _, is_prefix_nil _⟩⟩
  | star_step c1 evs c2 tr2 c3 Hss Hrest IH =>
    intro ms model Heq HM
    subst Heq
    have HM0 := HM
    obtain ⟨Hfd0, Hfd1, Hh, Hlazy⟩ := HM0
    have Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model := fd1chan_fdchan model Hfd1
    refine ⟨?_, ?_⟩
    · -- phase A: on the way to / at the read
      intro Hrd
      cases Hrd with
      | trd_here _ HRP =>
        -- at the read ecall
        obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hex, Hbytes⟩ := HRP
        rcases sstep_read_inv cnt Hcnt segs ms model buf x8 w evs (SNext c2)
            Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss with
          ⟨Hs, Hevs, Hc2⟩ | ⟨bs, Hlo, Hhi, Hpre, Hevs, Hc2⟩
        · -- end of input: the rest of the run is the exit tail
          cases Hc2
          subst Hevs
          rcases to_exit_star_only segs (Z_to_bv 64 0)
              (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model
              Hh Hlazy Hex tr2 c3 Hrest with h | h
          · subst h
            exact ⟨[], m_stdin model, chunks.chunks_nil _, is_prefix_nil _⟩
          · subst h
            refine ⟨[], m_stdin model, chunks.chunks_nil _, ?_⟩
            rw [Hs, band0_255]
            exact is_prefix_refl _
        · -- bytes: the rest of the run is a write-all phase
          cases Hc2
          subst Hevs
          have Hnb : 1 ≤ bs.length := by omega
          have Hbmbs : buf_modeled bs := by
            unfold buf_modeled
            omega
          obtain ⟨blocks, s', HCb, Hp⟩ :=
            (IH _ _ rfl (M_loop_take bs.length model HM)).2 bs Hnb Hbmbs
              (to_wr_wall_tail segs LH bs _ (Hbytes bs Hlo Hhi))
          refine ⟨bs :: blocks, s', chunks.chunks_cons _ bs blocks s' Hlo Hhi Hpre HCb, ?_⟩
          rw [List.flatMap_cons]
          unfold iter_ev iter_ev_ch
          rw [List.append_assoc, List.append_assoc]
          exact is_prefix_app_mono _ _ _ Hp
      | trd_step _ ms' Hsvc Hstep Hrd' =>
        -- an ordinary instruction
        obtain ⟨Hevs, Hc2⟩ :=
          sstep_instr_inv segs ms model ms' evs (SNext c2) Hlazy Hsvc Hstep Hss
        cases Hc2
        subst Hevs
        exact (IH _ model rfl HM).1 Hrd'
    · -- phase B: inside the echo write-all (retry) loop
      intro bs Hnb Hbm Hwt
      cases Hwt with
      | twt_done _ _ _ =>
        -- twt_done: the remainder is [], contradicting nonemptiness
        exact absurd Hnb (Nat.not_succ_le_zero 0)
      | twt_more _ _ _ _ Hwl =>
        -- twt_more: at the write ecall
        obtain ⟨n, Hn1, Hn2, Hevs, Hc2, Hwt2⟩ :=
          sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 ms bs (lh_next segs LH)
            model evs (SNext c2) Hh Hlazy Hfdc Hbm Hwl Hss
        cases Hc2
        subst Hevs
        by_cases hne : n = bs.length
        · -- full delivery: the remainder is empty; back to the read
          subst hne
          rw [List.drop_length] at Hwt2
          obtain ⟨msL, HmL, HlhL⟩ :=
            to_wall_tail_nil_msteps segs (Z_to_bv 64 1) _ (lh_next segs LH) Hwt2
          obtain ⟨blocks, s', HCb, Hp⟩ := (IH _ model rfl HM).1
            (msteps_to_rd segs LH cnt _ msL HmL (lh_next_to_rd segs LH cnt H_LH msL HlhL))
          refine ⟨blocks, s', HCb, ?_⟩
          rw [List.take_length]
          exact is_prefix_app_mono _ _ _ Hp
        · -- short delivery: the remainder is a shorter write-all phase
          have Hnb' : 1 ≤ (bs.drop n).length := by
            rw [List.length_drop]
            omega
          obtain ⟨blocks, s', HCb, Hp⟩ := (IH _ model rfl HM).2 (bs.drop n) Hnb'
            (buf_modeled_skipn n bs Hbm) Hwt2
          refine ⟨blocks, s', HCb, ?_⟩
          have heq : List.map (WriteEv (Z_to_bv 64 1)) bs ++
                (List.flatMap iter_ev blocks ++ eof_tail s' (m_fs model)) =
              List.map (WriteEv (Z_to_bv 64 1)) (bs.take n) ++
                (List.map (WriteEv (Z_to_bv 64 1)) (bs.drop n) ++
                  (List.flatMap iter_ev blocks ++ eof_tail s' (m_fs model))) := by
            rw [← List.append_assoc (List.map (WriteEv (Z_to_bv 64 1)) (bs.take n)),
              ← List.map_append, List.take_append_drop]
          rw [heq]
          exact is_prefix_app_mono _ _ _ Hp
      | twt_step _ msS' _ _ HsvcS HstepS Hwt' =>
        -- twt_step: an ordinary instruction
        obtain ⟨Hevs, Hc2⟩ :=
          sstep_instr_inv segs ms model msS' evs (SNext c2) Hlazy HsvcS HstepS Hss
        cases Hc2
        subst Hevs
        exact (IH _ model rfl HM).2 bs Hnb Hbm Hwt'

/-! ### No error: the phase invariant -/

/-- The loop's phase invariant: the model is the loop's (`M_loop`) and the
machine is on its way to the read or inside the echo write-all phase, or
the run is on the exit(0) straight line (`ExitSim.on_path`). -/
def sinv (segs : List Segment) (LH : machine_state → Prop) (cnt : word) (c : config) : Prop :=
  (M_loop c.cfg_model ∧
    (to_rd segs LH cnt c.cfg_ms ∨
      ∃ bs, 1 ≤ bs.length ∧ buf_modeled bs ∧
        to_wall_tail segs (Z_to_bv 64 1) c.cfg_ms bs (lh_next segs LH)))
  ∨ on_path segs (Z_to_bv 64 0) c

open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Common.SimInv

theorem sinv_step (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (c : config) (evs : List event) (c' : config)
    (Hinv : sinv segs LH cnt c) (Hss : sstep segs c evs (SNext c')) :
    sinv segs LH cnt c' := by
  obtain ⟨ms, model⟩ := c
  obtain ⟨ms', model'⟩ := c'
  rcases Hinv with ⟨HM, Hphase⟩ | Hop
  · obtain ⟨Hfd0, Hfd1, Hh, Hlazy⟩ := HM
    have Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model := fd1chan_fdchan model Hfd1
    rcases Hphase with Hrd | ⟨bs, Hnb, Hbm, Hwt⟩
    · cases Hrd with
      | trd_here _ HRP =>
        obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hex, Hbytes⟩ := HRP
        rcases sstep_read_inv cnt Hcnt segs ms model buf x8 w evs _
            Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss with
          ⟨_, _, Hc2⟩ | ⟨bs, Hlo, Hhi, _, _, Hc2⟩
        · cases Hc2
          exact Or.inr (Or.inl ⟨Hh, Hlazy, Hex⟩)
        · cases Hc2
          refine Or.inl ⟨M_loop_take bs.length model ⟨Hfd0, Hfd1, Hh, Hlazy⟩, Or.inr ⟨bs, ?_, ?_,
            to_wr_wall_tail segs LH bs _ (Hbytes bs Hlo Hhi)⟩⟩
          · omega
          · unfold buf_modeled
            omega
      | trd_step _ ms1 Hsvc Hstep Hrd' =>
        obtain ⟨_, Hc2⟩ := sstep_instr_inv segs ms model ms1 evs _ Hlazy Hsvc Hstep Hss
        cases Hc2
        exact Or.inl ⟨⟨Hfd0, Hfd1, Hh, Hlazy⟩, Or.inl Hrd'⟩
    · cases Hwt with
      | twt_done _ _ _ =>
        -- the remainder is `[]`, contradicting nonemptiness
        exact absurd Hnb (Nat.not_succ_le_zero 0)
      | twt_more _ _ _ _ Hwl =>
        -- at the write ecall
        obtain ⟨n, Hn1, Hn2, _, Hc2, Hwt2⟩ :=
          sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 ms bs (lh_next segs LH)
            model evs _ Hh Hlazy Hfdc Hbm Hwl Hss
        cases Hc2
        by_cases Hne : n = bs.length
        · -- full delivery: back to the read phase
          subst Hne
          rw [List.drop_length] at Hwt2
          obtain ⟨msL, HmL, HlhL⟩ := to_wall_tail_nil_msteps segs (Z_to_bv 64 1) _ _ Hwt2
          exact Or.inl ⟨⟨Hfd0, Hfd1, Hh, Hlazy⟩,
            Or.inl (msteps_to_rd segs LH cnt _ msL HmL (lh_next_to_rd segs LH cnt H_LH msL HlhL))⟩
        · -- short delivery: a shorter write-all phase
          refine Or.inl ⟨⟨Hfd0, Hfd1, Hh, Hlazy⟩, Or.inr ⟨bs.drop n, ?_,
            buf_modeled_skipn n bs Hbm, Hwt2⟩⟩
          rw [List.length_drop]
          omega
      | twt_step _ msS' _ _ HsvcS HstepS Hwt' =>
        obtain ⟨_, Hc2⟩ := sstep_instr_inv segs ms model msS' evs _ Hlazy HsvcS HstepS Hss
        cases Hc2
        exact Or.inl ⟨⟨Hfd0, Hfd1, Hh, Hlazy⟩, Or.inr ⟨bs, Hnb, Hbm, Hwt'⟩⟩
  · exact Or.inr (on_path_step segs (Z_to_bv 64 0) _ evs _ Hop Hss)

theorem sinv_no_error (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (c : config) (evs : List event) (Hinv : sinv segs LH cnt c) :
    ¬ sstep segs c evs SError := by
  intro Hss
  obtain ⟨ms, model⟩ := c
  rcases Hinv with ⟨HM, Hphase⟩ | Hop
  · obtain ⟨Hfd0, Hfd1, Hh, Hlazy⟩ := HM
    have Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model := fd1chan_fdchan model Hfd1
    rcases Hphase with Hrd | ⟨bs, Hnb, Hbm, Hwt⟩
    · cases Hrd with
      | trd_here _ HRP =>
        obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, _, _⟩ := HRP
        rcases sstep_read_inv cnt Hcnt segs ms model buf x8 w evs SError
            Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss with
          ⟨_, _, Hc2⟩ | ⟨_, _, _, _, _, Hc2⟩
        · cases Hc2
        · cases Hc2
      | trd_step _ ms1 Hsvc Hstep _ =>
        obtain ⟨_, Hc2⟩ := sstep_instr_inv segs ms model ms1 evs SError Hlazy Hsvc Hstep Hss
        cases Hc2
    · cases Hwt with
      | twt_done _ _ _ => exact absurd Hnb (Nat.not_succ_le_zero 0)
      | twt_more _ _ _ _ Hwl =>
        exact to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
          ms bs (lh_next segs LH) model evs Hh Hlazy Hfdc Hbm Hwl Hss
      | twt_step _ msS' _ _ HsvcS HstepS _ =>
        obtain ⟨_, Hc2⟩ := sstep_instr_inv segs ms model msS' evs SError Hlazy HsvcS HstepS Hss
        cases Hc2
  · exact on_path_no_error segs (Z_to_bv 64 0) _ evs Hop Hss

/-! ## Whole-run packaging from the initial state -/

theorem stream_obs_iff (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput)
    (Hrd : to_rd segs LH cnt (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap))
    (tr : List event) :
    obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
      stream_traces cnt inp.in_fs inp.in_stdin tr := by
  have HM0 := init_M_loop (segments_reserved segs) brk0 mb sp lim inp
  constructor
  · intro Hobs
    obtain ⟨tr', c, Hstar, Hp⟩ := Hobs
    obtain ⟨blocks, s', HC, Hp'⟩ :=
      (star_loop_only segs LH cnt Hcnt H_LH _ tr' c Hstar _ _ rfl HM0).1 Hrd
    exact stream_traces_prefix_closed cnt inp.in_fs inp.in_stdin tr' tr ⟨blocks, s', HC, Hp'⟩ Hp
  · intro Hst
    obtain ⟨blocks, s', HC, Hp⟩ := Hst
    obtain ⟨c, Hstar⟩ :=
      stream_star_admits segs LH cnt Hcnt H_LH inp.in_stdin blocks s' HC _ _ HM0 rfl Hrd
    exact ⟨List.flatMap iter_ev blocks ++ eof_tail s' inp.in_fs, c, Hstar, Hp⟩

/-! ## The omni reading

A stream loop need not terminate (the input stream is coinductive), so its
judgments are the coinductive pair: the loop invariant IS a proof of
`OmniRun.coexec … never_errors`, by coinduction along `sinv_step` and with no
`Run.star` in sight, and the trace characterisation is the prefix judgment
`OmniRun.cosafe`. -/

theorem to_rd_coexec (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (ms : machine_state) (model : Model) (HM : M_loop model) (Hrd : to_rd segs LH cnt ms) :
    coexec segs (config.mkCfg ms model) never_errors :=
  inv_coexec segs (sinv segs LH cnt) (sinv_step segs LH cnt Hcnt H_LH)
    (sinv_no_error segs LH cnt Hcnt) _ (Or.inl ⟨HM, Or.inl Hrd⟩)

theorem stream_omni_corun (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput)
    (Hrd : to_rd segs LH cnt (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
      inp.in_uid inp.in_hwcap)) :
    omni_corun (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp
      never_errors :=
  to_rd_coexec segs LH cnt Hcnt H_LH _ _
    (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) Hrd

/-! ## Pair equivalence

The characterization `stream_traces cnt fs0 stdin0` does not mention the
binary, so two binaries that both satisfy it are equivalent — ON THE SAME
INPUT STREAM, which is what the theorem shape quantifies over. -/

/-- The omni equivalence of two stream loops on the same input stream, at the
two role budgets. -/
theorem stream_omni_strong_equiv (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (source_segs : List Segment) (rLH : machine_state → Prop) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (aLH : machine_state → Prop) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (inp : ProcInput)
    (HrLH : ∀ ms, rLH ms → to_rd source_segs rLH cnt ms)
    (HaLH : ∀ ms, aLH ms → to_rd target_segs aLH cnt ms)
    (Hr : to_rd source_segs rLH cnt (init_machine_state source_segs rpc rph rsp rrnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap))
    (Ha : to_rd target_segs aLH cnt (init_machine_state target_segs apc aph asp arnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)) :
    omni_strong_equiv (Image.mkImage source_segs rpc rph) (Image.mkImage target_segs apc aph)
      (ExecEntry.mkEntry rsp rbrk rmb rrnd) (ExecEntry.mkEntry asp abrk amb arnd) inp := by
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · exact coexec_conseq _ _ _ _
      (stream_omni_corun source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd
        source_alloc_limit inp Hr)
      (never_errors_covered _)
  · refine (trace_equiv_iff_omni _ _ _ _ _ _ _).1 ?_
    intro tr
    exact (stream_obs_iff source_segs rLH cnt Hcnt HrLH
        rpc rph rsp rbrk rmb rrnd source_alloc_limit inp Hr tr).trans
      (stream_obs_iff target_segs aLH cnt Hcnt HaLH
        apc aph asp abrk amb arnd target_alloc_limit inp Ha tr).symm
  · exact stream_omni_corun target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb
      arnd target_alloc_limit inp Ha

end LinuxProcessSemantics.Common.StreamSim

/-! ## Additions for E-proof-library-2b

Ported from `theories/Common/StreamSim.v` with the Rocq statements, for
ticket E-proof-library-2b, and appended under the lead's ruling of
2026-09-29 on #1298's files: the declarations above are unchanged.  The
Rocq file is unchanged from the commit the header names to the day tip
f62e8cc14; 62d810d34 was the last commit to change it.

`Common/DrainSim.lean`'s `drain_obs_iff` reaches these: its aborting
branch reads its last block back out of the chunking, through
`chunks_split` and `chunks_single_inv`.  The header above lists both among
the names #1298 left unported; that list predates this section. -/

namespace LinuxProcessSemantics.Common.StreamSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State

/-- A chunking of `l1 ++ l2` is a chunking of `l1` followed by one of
`l2`. -/
theorem chunks_split (cnt : word) (l1 l2 : List (List byte)) (s s2 : InputStream)
    (H : chunks cnt s (l1 ++ l2) s2) :
    ∃ s1, chunks cnt s l1 s1 ∧ chunks cnt s1 l2 s2 := by
  induction l1 generalizing s with
  | nil => exact ⟨s, chunks.chunks_nil s, H⟩
  | cons bs l1 IH =>
    rw [List.cons_append] at H
    cases H with
    | chunks_cons _ _ _ _ Hlo Hhi Hpre HC =>
      obtain ⟨s1, H1, H2⟩ := IH _ HC
      exact ⟨s1, chunks.chunks_cons s bs l1 s1 Hlo Hhi Hpre H1, H2⟩

/-- Inversion for a one-block chunking. -/
theorem chunks_single_inv (cnt : word) (s : InputStream) (bs : List byte) (s' : InputStream)
    (H : chunks cnt s [bs] s') :
    1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ bv_unsigned cnt ∧
      (stream_take s bs.length).1 = bs ∧ s' = (stream_take s bs.length).2 := by
  cases H with
  | chunks_cons _ _ _ _ Hlo Hhi Hpre HC =>
    cases HC with
    | chunks_nil _ => exact ⟨Hlo, Hhi, Hpre, rfl⟩

end LinuxProcessSemantics.Common.StreamSim
