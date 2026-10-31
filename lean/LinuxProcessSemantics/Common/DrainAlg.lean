import LinuxProcessSemantics.Common.ShapeAlg
import LinuxProcessSemantics.Common.StreamSim

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b
-/

/-! # Common.DrainAlg — read nodes and bounded drain shapes

PROOF-SIDE, not part of the trusted specification. This image-independent
library packages StreamSim's read outcomes as an exact ShapeAlg node and
realizes a bounded drain with a continuation parameter. Unlike an unbounded
drain, which can keep reading an infinite stream and cannot have an inductive
`realizes` derivation, this loop stops at EOF or capacity. Each nonempty block
consumes capacity, so structural fuel suffices on every stream. The collapse
lemmas erase chunk boundaries: emit the first capacity-many input bytes, then
run the tail on those bytes. No unbounded drain realization is asserted here.

Rocq `Z` is `Int`, `nat` is `Nat`, bytes and words retain widths 8 and 64,
and section parameters are explicit leading arguments, only where used.
`stream_cases` replaces coinductive constructor case analysis; it imposes no
finiteness restriction. Read fd/count checks retain their integer statements.
-/

namespace LinuxProcessSemantics.Common.DrainAlg

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Run.config
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.StreamSim
open LinuxProcessSemantics.Common.ShapeAlg
open LinuxProcessSemantics.Common.ShapeAlg.realizes
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.MmapSim
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap

/-- The resolutions of a `read(0, buf, cnt)` against remaining input `s`.
`StreamSim.read0_ok_inv` says these are exactly the model's outcomes. -/
def rd_adm (s : InputStream) (cnt : word) (bs : List byte) : Prop :=
  (bs = [] ∧ s = IEof) ∨
    (1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ bv_unsigned cnt ∧
      (stream_take s bs.length).1 = bs)

def RdIdx (s : InputStream) (cnt : word) : Type := { bs : List byte // rd_adm s cnt bs }

/-- Every read has at least one resolution: EOF, or the one-byte block. -/
theorem rd_adm_inhab (s : InputStream) (cnt : word) (Hcnt : 0 < bv_unsigned cnt) :
    ∃ bs, rd_adm s cnt bs := by
  rcases stream_cases s with rfl | ⟨b, s', rfl⟩
  · exact ⟨[], Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨[b], Or.inr ⟨by change (1 : Int) ≤ 1; omega, by change (1 : Int) ≤ bv_unsigned cnt; omega, rfl⟩⟩

theorem rd_adm_eof_nil (s : InputStream) (cnt : word) (bs : List byte)
    (H : rd_adm s cnt bs) (Hnil : bs = []) : s = IEof := by
  rcases H with ⟨_, Hs⟩ | ⟨Hlo, _, _⟩
  · exact Hs
  · subst bs
    simp only [List.length_nil, Int.natCast_zero] at Hlo
    omega

/-- A block resolution is nonempty. -/
theorem rd_adm_block_nonnil (bs : List byte) (H : 1 ≤ (bs.length : Int)) : bs ≠ [] := by
  intro heq
  subst bs
  simp only [List.length_nil, Int.natCast_zero] at H
  omega

/-- The successor configuration of a read resolution. The match on `bs`
is exhaustive and non-overlapping: EOF returns zero bytes, every block
is nonempty. -/
def rd_next (ms : machine_state) (model : Model) (buf : word) (bs : List byte) : config :=
  match bs with
  | [] => config.mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model
  | _ :: _ => config.mkCfg
      (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] [])))
      (with_stdin (stream_take (m_stdin model) bs.length).2 model)

theorem rd_next_stdin_block (ms : machine_state) (model : Model) (buf : word)
    (bs : List byte) (H : bs ≠ []) :
    m_stdin (cfg_model (rd_next ms model buf bs)) = (stream_take (m_stdin model) bs.length).2 := by
  cases bs with
  | nil => exact False.elim (H rfl)
  | cons _ _ => rfl

/-- The list of bytes an `InputStream` delivers in its first `k`. -/
def stream_firstn (s : InputStream) (k : Nat) : List byte := (stream_take s k).1

theorem stream_take_split (k1 k2 : Nat) (s : InputStream) :
    (stream_take s (k1 + k2)).1 =
      (stream_take s k1).1 ++ (stream_take (stream_take s k1).2 k2).1 :=
  congrArg Prod.fst (stream_take_add k1 k2 s)

theorem stream_take_cons_pos (b : byte) (s : InputStream) (k : Nat) (H : 1 ≤ k) :
    (stream_take (ICons b s) k).1 = b :: (stream_take s (k - 1)).1 := by
  cases k with
  | zero => omega
  | succ k => exact congrArg Prod.fst (stream_take_cons b s k)

theorem stream_take_ge (k1 k2 : Nat) (s : InputStream) (Hle : k1 ≤ k2)
    (Hlen : (stream_take s k1).1.length < k1) :
    (stream_take s k2).1 = (stream_take s k1).1 := by
  induction k1 generalizing k2 s with
  | zero => omega
  | succ k1 IH =>
    cases k2 with
    | zero => omega
    | succ k2 =>
      rcases stream_cases s with rfl | ⟨b, s', rfl⟩
      · simp only [stream_take_eof]
      · simp only [stream_take_cons, List.length_cons] at Hlen ⊢
        rw [IH k2 s' (by omega) (by omega)]

/-- Whatever chunking the loop takes, it exits with exactly the first
`cap` bytes of the stream (or all of them, if there are fewer). This is
why the tail is a function of the input despite nondeterministic reads. -/
theorem stream_take_app_take (s : InputStream) (bs : List byte) (k : Nat)
    (Hpre : (stream_take s bs.length).1 = bs) :
    bs ++ (stream_take (stream_take s bs.length).2 k).1 =
      (stream_take s (bs.length + k)).1 := by
  rw [stream_take_split, Hpre]

/-- The `read(0, buf, cnt)` node: its transitions are exactly the
`RdIdx`-indexed family. Clause 1 is `StreamSim.read0_ok_eof` /
`read0_ok_bytes`; clause 2 is `StreamSim.sstep_read_inv`. -/
theorem node_read0 (segs : List Segment) (ms : machine_state) (model : Model)
    (buf cnt x8 : word) (w : List byte)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 63)
    (Hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (Hg1 : ms_gpr ms 1 = buf)
    (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) buf cnt = some w)
    (Haok : access_okb buf (bv_unsigned cnt) = true) :
    node_ok segs (config.mkCfg ms model) (RdIdx (m_stdin model) cnt)
      (fun i => i.val.map (ReadEv (Z_to_bv 64 0))) (fun i => rd_next ms model buf i.val) := by
  constructor
  · rintro ⟨bs, Hadm⟩
    rcases Hadm with ⟨rfl, Heof⟩ | ⟨Hlo, Hhi, Hpre⟩
    · change sstep segs (config.mkCfg ms model) []
        (SNext (config.mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model))
      rw [← apply_effect_no_write ms (Z_to_bv 64 0)]
      exact sstep.sstep_syscall ms model x8 _ model model [] Hh Hsvc
        (read0_ok_eof cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2
          (by rw [Hg1]; exact Hw) (by rw [Hg1]; exact Haok)) Hh
        (materialize_model_accesses_no_lazy _ _ Hlazy)
    · cases bs with
      | nil => simp only [List.length_nil, Int.natCast_zero] at Hlo; omega
      | cons b bs =>
        apply sstep.sstep_syscall ms model x8 _ _ _ _ Hh Hsvc
        · have h := read0_ok_bytes cnt Hcnt segs ms x8 model w (b :: bs) Hno Hfd Hg0 Hg2
            (by rw [Hg1]; exact Hw) (by rw [Hg1]; exact Haok) Hlo Hhi Hpre
          rw [Hg1] at h
          exact h
        · exact Hh
        · exact materialize_model_accesses_no_lazy _ _ ((m_vm_lazy_with_stdin _ _).trans Hlazy)
  · intro e st Hss
    rcases sstep_read_inv cnt Hcnt segs ms model buf x8 w e st
      Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss with
      ⟨Heof, rfl, rfl⟩ | ⟨bs, Hlo, Hhi, Hpre, rfl, rfl⟩
    · exact ⟨⟨[], Or.inl ⟨rfl, Heof⟩⟩, rfl, rfl⟩
    · refine ⟨⟨bs, Or.inr ⟨Hlo, Hhi, Hpre⟩⟩, rfl, ?_⟩
      cases bs with
      | nil => simp only [List.length_nil, Int.natCast_zero] at Hlo; omega
      | cons _ _ => rfl

/-- The trace set of a read node on channel `rch`: choose a resolution,
emit its `ReadEv`s, continue as `K bs`. The write-side twin is
`ShapeAlg.t_write_ch`. -/
def t_read_ch (rch : word) (s : InputStream) (cnt : word) (K : List byte → TSet) : TSet :=
  t_alt (fun i : RdIdx s cnt => t_emit (i.val.map (ReadEv rch)) (K i.val))

/-- The same node on channel 0, the only channel a read can name:
`ReadWrite.read_spec` answers -EBADF on the rest directly, and
`ReadWrite.readv_spec` does so through `ReadWrite.readable_fd`.
This is the form `rz_read0` realizes. -/
def t_read0 (s : InputStream) (cnt : word) (K : List byte → TSet) : TSet :=
  t_read_ch (Z_to_bv 64 0) s cnt K

/-- The introduction rule. Continuation-polymorphic, like every other
combinator in `ShapeAlg`. -/
theorem rz_read0 (segs : List Segment) (ms : machine_state) (model : Model)
    (buf cnt x8 : word) (w : List byte) (K : List byte → TSet)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 63)
    (Hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (Hg1 : ms_gpr ms 1 = buf)
    (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) buf cnt = some w)
    (Haok : access_okb buf (bv_unsigned cnt) = true)
    (HK : ∀ bs, rd_adm (m_stdin model) cnt bs → realizes segs (rd_next ms model buf bs) (K bs)) :
    realizes segs (config.mkCfg ms model) (t_read0 (m_stdin model) cnt K) := by
  obtain ⟨bs0, Hbs0⟩ := rd_adm_inhab (m_stdin model) cnt Hcnt.1
  exact rz_node _ (RdIdx (m_stdin model) cnt) _ _ _ ⟨bs0, Hbs0⟩
    (node_read0 segs ms model buf cnt x8 w Hcnt Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok)
    (fun i => HK i.val i.property)

/-- Emitting `a` then `b` is emitting `a ++ b`. Purely about `t_emit`;
it belongs next to `ShapeAlg.t_emit_nil_eq`, but ShapeAlg is unchanged. -/
theorem t_emit_app (a b : List event) (T : TSet) :
    t_eq (t_emit a (t_emit b T)) (t_emit (a ++ b) T) := by
  intro tr
  constructor
  · rintro (Hp | ⟨tr', rfl, Hp | ⟨tr'', rfl, HT⟩⟩)
    · exact Or.inl (is_prefix_app_r _ _ _ Hp)
    · exact Or.inl (is_prefix_app_mono _ _ _ Hp)
    · exact Or.inr ⟨tr'', (List.append_assoc ..).symm, HT⟩
  · rintro (Hp | ⟨tr', rfl, HT⟩)
    · rcases is_prefix_app_split a b tr Hp with Hpart | ⟨tr', heq, Hpart⟩
      · exact Or.inl Hpart
      · exact Or.inr ⟨tr', heq, Or.inl Hpart⟩
    · exact Or.inr ⟨b ++ tr', List.append_assoc .., Or.inr ⟨tr', rfl, HT⟩⟩

/-- `t_emit` respects `t_eq` in its continuation. `t_eq` is not a
registered setoid relation, so this replaces a rewrite. -/
theorem t_emit_cong (e : List event) (T T' : TSet) (H : t_eq T T') :
    t_eq (t_emit e T) (t_emit e T') := by
  intro tr
  constructor
  · rintro (Hp | ⟨tr', heq, HT⟩)
    · exact Or.inl Hp
    · exact Or.inr ⟨tr', heq, (H tr').1 HT⟩
  · rintro (Hp | ⟨tr', heq, HT⟩)
    · exact Or.inl Hp
    · exact Or.inr ⟨tr', heq, (H tr').2 HT⟩

/-- The count word of the next read at loop head `acc`.
The arena capacity `cap` bounds reads by the space remaining; the loop
stops at capacity or EOF, whichever comes first. -/
def dcnt (cap : Nat) (acc : List byte) : word := Z_to_bv 64 (cap - acc.length : Nat)

theorem dcnt_pos (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64) (acc : List byte)
    (H : acc.length < cap) : 0 < bv_unsigned (dcnt cap acc) := by
  unfold dcnt
  rw [Z_to_bv_unsigned, bv_wrap, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-- Each read is capped by what is left of `cap`, which is at most
`Uaccess.rw_bytes_max`, the model's read bound. -/
theorem dcnt_max (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Hcap_modeled : (cap : Int) ≤ rw_bytes_max) (acc : List byte) (H : acc.length ≤ cap) :
    bv_unsigned (dcnt cap acc) ≤ rw_bytes_max := by
  unfold dcnt
  rw [Z_to_bv_unsigned, bv_wrap, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem dcnt_val (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64) (acc : List byte)
    (H : acc.length ≤ cap) : bv_unsigned (dcnt cap acc) = (cap - acc.length : Nat) := by
  unfold dcnt
  rw [Z_to_bv_unsigned, bv_wrap, Int.emod_eq_of_lt (by omega) (by omega)]

/-- The loop's trace set. `n` is structural fuel: a resolution consumes
`bs.length` capacity rather than exactly one. `rz_drain_top` uses `cap`;
the invariant `cap - acc.length ≤ n`, preserved because blocks are nonempty,
ensures fuel never cuts the loop short. `Tfin` is the shape of everything
after the loop, as a function of the accumulated bytes. -/
def t_drain_ch (cap : Nat) (Tfin : List byte → TSet) (rch : word)
    (n : Nat) (s : InputStream) (acc : List byte) : TSet :=
  match n with
  | 0 => Tfin acc
  | n' + 1 =>
    if cap ≤ acc.length then Tfin acc
    else t_read_ch rch s (dcnt cap acc) (fun bs =>
      match bs with
      | [] => Tfin acc
      | _ :: _ => t_drain_ch cap Tfin rch n' (stream_take s bs.length).2 (acc ++ bs))

/-- The loop at channel 0, which a binary realizes. This definition wraps
`t_drain_ch`: unfolding an iteration uses both `t_drain` and `t_drain_ch`,
not just the wrapper. -/
def t_drain (cap : Nat) (Tfin : List byte → TSet) (n : Nat)
    (s : InputStream) (acc : List byte) : TSet :=
  t_drain_ch cap Tfin (Z_to_bv 64 0) n s acc

/-- A read emits one `ReadEv` per byte, so chunking contributes the same
mapped concatenation regardless of syscall boundaries. The loop therefore
denotes a single shape: emit the first `cap - acc.length` remaining bytes,
then run the tail on the resulting arena. Different read chunkings have the
same shape, and the tail is a function of the input.

The tail is nonempty (`Htfin_ne`), automatically true for a shape a binary
realizes (`ShapeAlg.realizes_nonempty`); stating it here makes the collapse
a fact about trace sets alone. -/
theorem t_drain_ch_collapse (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Tfin : List byte → TSet) (Htfin_ne : ∀ acc, Tfin acc [])
    (rch : word) (n : Nat) (s : InputStream) (acc : List byte)
    (Hn : cap - acc.length ≤ n) (Hle : acc.length ≤ cap) :
    t_eq (t_drain_ch cap Tfin rch n s acc)
      (t_emit ((stream_take s (cap - acc.length)).1.map (ReadEv rch))
        (Tfin (acc ++ (stream_take s (cap - acc.length)).1))) := by
  induction n generalizing s acc with
  | zero =>
    have hz : cap - acc.length = 0 := by omega
    simp only [t_drain_ch, hz, stream_take_zero, List.map_nil, List.append_nil]
    exact t_eq_sym _ _ (t_emit_nil_eq _ (Htfin_ne acc))
  | succ n IH =>
    simp only [t_drain_ch]
    by_cases Hfull : cap ≤ acc.length
    · have hz : cap - acc.length = 0 := by omega
      simp only [Hfull, ↓reduceIte, hz, stream_take_zero, List.map_nil, List.append_nil]
      exact t_eq_sym _ _ (t_emit_nil_eq _ (Htfin_ne acc))
    · simp only [Hfull, ↓reduceIte]
      let m := cap - acc.length
      have Hm : 1 ≤ m := by dsimp only [m]; omega
      have Hdc : bv_unsigned (dcnt cap acc) = (m : Int) := dcnt_val cap Hcap acc Hle
      intro tr
      constructor
      · rintro ⟨⟨bs, Hadm⟩, Hi⟩
        cases bs with
        | nil =>
          have Heof := rd_adm_eof_nil s (dcnt cap acc) [] Hadm rfl
          subst s
          simpa only [stream_take_nil_of_eof, List.map_nil, List.append_nil] using Hi
        | cons b bs =>
          rcases Hadm with ⟨Hbad, _⟩ | ⟨Hlo, Hhi, Hpre⟩
          · cases Hbad
          · have Hblen : (b :: bs).length ≤ m := by rw [Hdc] at Hhi; omega
            have Hsplit : (stream_take s m).1 = (b :: bs) ++
                (stream_take (stream_take s (b :: bs).length).2 (m - (b :: bs).length)).1 := by
              calc
                (stream_take s m).1 =
                    (stream_take s ((b :: bs).length + (m - (b :: bs).length))).1 := by
                  congr 2; omega
                _ = _ := by rw [stream_take_split, Hpre]
            have Hlen : (acc ++ b :: bs).length = acc.length + (b :: bs).length := List.length_append ..
            have IHb := IH (stream_take s (b :: bs).length).2 (acc ++ b :: bs)
              (by dsimp only [m] at Hblen; simp only [List.length_cons] at Hlen ⊢; omega)
              (by dsimp only [m] at Hblen; omega)
            have Hrem : cap - (acc ++ b :: bs).length = m - (b :: bs).length := by
              dsimp only [m]; omega
            rw [Hrem, List.append_assoc] at IHb
            change t_emit ((stream_take s m).1.map (ReadEv rch))
              (Tfin (acc ++ (stream_take s m).1)) tr
            rw [Hsplit, List.map_append]
            exact (t_emit_app _ _ _ tr).1 ((t_emit_cong _ _ _ IHb tr).1 Hi)
      · intro Hrhs
        rcases stream_cases s with rfl | ⟨b, s', rfl⟩
        · refine ⟨⟨[], Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
          simpa only [stream_take_nil_of_eof, List.map_nil, List.append_nil] using Hrhs
        · have Hadm : rd_adm (ICons b s') (dcnt cap acc) [b] :=
            Or.inr ⟨by change (1 : Int) ≤ 1; omega,
              by change (1 : Int) ≤ bv_unsigned (dcnt cap acc); rw [Hdc]; omega, rfl⟩
          refine ⟨⟨[b], Hadm⟩, ?_⟩
          have Hlen : (acc ++ [b]).length = acc.length + 1 := by
            simp only [List.length_append, List.length_cons, List.length_nil]
          have IHb := IH s' (acc ++ [b]) (by omega) (by omega)
          have Hrem : cap - (acc ++ [b]).length = m - 1 := by dsimp only [m]; omega
          rw [Hrem, List.append_assoc] at IHb
          apply (t_emit_cong [ReadEv rch b] _ _ IHb tr).2
          apply (t_emit_app [ReadEv rch b] _ _ tr).2
          change t_emit ((stream_take (ICons b s') m).1.map (ReadEv rch))
            (Tfin (acc ++ (stream_take (ICons b s') m).1)) tr at Hrhs
          rw [stream_take_cons_pos b s' m Hm] at Hrhs
          exact Hrhs

/-- The collapse at channel 0, which is the form a binary uses. -/
theorem t_drain_collapse (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Tfin : List byte → TSet) (Htfin_ne : ∀ acc, Tfin acc [])
    (n : Nat) (s : InputStream) (acc : List byte)
    (Hn : cap - acc.length ≤ n) (Hle : acc.length ≤ cap) :
    t_eq (t_drain cap Tfin n s acc)
      (t_emit ((stream_take s (cap - acc.length)).1.map (ReadEv (Z_to_bv 64 0)))
        (Tfin (acc ++ (stream_take s (cap - acc.length)).1))) :=
  t_drain_ch_collapse cap Hcap Tfin Htfin_ne (Z_to_bv 64 0) n s acc Hn Hle

/-- The same collapse at the loop's entry, with an empty accumulator. -/
theorem t_drain_ch_top_collapse (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Tfin : List byte → TSet) (Htfin_ne : ∀ acc, Tfin acc []) (rch : word) (s : InputStream) :
    t_eq (t_drain_ch cap Tfin rch cap s [])
      (t_emit ((stream_firstn s cap).map (ReadEv rch)) (Tfin (stream_firstn s cap))) := by
  exact t_drain_ch_collapse cap Hcap Tfin Htfin_ne rch cap s [] (by omega) (by exact Nat.zero_le cap)

/-- The collapse at loop entry on channel 0, as used by a binary
(`Examples.arena_tee_ns` in the Rocq tree). -/
theorem t_drain_top_collapse (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Tfin : List byte → TSet) (Htfin_ne : ∀ acc, Tfin acc []) (s : InputStream) :
    t_eq (t_drain cap Tfin cap s [])
      (t_emit ((stream_firstn s cap).map (ReadEv (Z_to_bv 64 0))) (Tfin (stream_firstn s cap))) :=
  t_drain_ch_top_collapse cap Hcap Tfin Htfin_ne (Z_to_bv 64 0) s

/-- The loop rule. Ordinary induction on fuel, with no coinduction or step
indexing, because capacity bounds the loop on every stream.

`LH` is the per-binary loop-head predicate indexed by bytes read so far.
`Hfull` exits the read loop at capacity. `Hread` is the single per-binary
obligation: with capacity left, silently run to a read whose EOF successor
runs the tail and whose nonempty successors return to the loop head. The
buffer is existential: only writability of the remaining count matters.
The access check is separate: mapped word arithmetic can wrap at 2^64,
whereas `access_okb` enforces the range check before input is consulted. -/
theorem rz_drain (segs : List Segment) (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Hcap_modeled : (cap : Int) ≤ rw_bytes_max)
    (LH : List byte → config → Prop) (Tfin : List byte → TSet)
    (Hfull : ∀ acc c, LH acc c → cap ≤ acc.length → realizes segs c (Tfin acc))
    (Hread : ∀ acc c, LH acc c → acc.length < cap →
      ∃ ms1 buf x8 w,
        m_halted (cfg_model c) = none ∧
        m_vm_lazy (cfg_model c) = [] ∧
        fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)) ∧
        msteps segs (cfg_ms c) ms1 ∧
        ms1.ms_svc_pending = some x8 ∧ bv_unsigned x8 = 63 ∧
        ms_gpr ms1 0 = Z_to_bv 64 0 ∧ ms_gpr ms1 1 = buf ∧
        ms_gpr ms1 2 = dcnt cap acc ∧
        read_bytes_map (ms_writable_byte segs ms1) buf (dcnt cap acc) = some w ∧
        access_okb buf (bv_unsigned (dcnt cap acc)) = true ∧
        realizes segs (rd_next ms1 (cfg_model c) buf []) (Tfin acc) ∧
        (∀ bs, rd_adm (m_stdin (cfg_model c)) (dcnt cap acc) bs → bs ≠ [] →
          LH (acc ++ bs) (rd_next ms1 (cfg_model c) buf bs)))
    (n : Nat) (acc : List byte) (c : config) (Hn : cap - acc.length ≤ n) (HLH : LH acc c) :
    realizes segs c (t_drain cap Tfin n (m_stdin (cfg_model c)) acc) := by
  induction n generalizing acc c with
  | zero => exact Hfull acc c HLH (by omega)
  | succ n IH =>
    simp only [t_drain, t_drain_ch]
    by_cases Hle : cap ≤ acc.length
    · simp only [Hle, ↓reduceIte]
      exact Hfull acc c HLH Hle
    · simp only [Hle, ↓reduceIte]
      have Hlt : acc.length < cap := by omega
      obtain ⟨ms1, buf, x8, w, Hh, Hlazy, Hfd, Hms, Hsvc, Hno, Hg0, Hg1, Hg2, Hw,
        Haok, Heof, Hblk⟩ := Hread acc c HLH Hlt
      cases c with
      | mkCfg ms0 model =>
        apply rz_msteps segs ms0 ms1 model _ Hh Hlazy Hms
        apply rz_read0 segs ms1 model buf (dcnt cap acc) x8 w _
          ⟨dcnt_pos cap Hcap acc Hlt, dcnt_max cap Hcap Hcap_modeled acc (by omega)⟩
          Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
        intro bs Hadm
        cases bs with
        | nil => exact Heof
        | cons b bs =>
          have Hne : b :: bs ≠ [] := List.cons_ne_nil _ _
          have hi := IH (acc ++ b :: bs) (rd_next ms1 model buf (b :: bs))
            (by simp only [List.length_append, List.length_cons]; omega) (Hblk _ Hadm Hne)
          rw [rd_next_stdin_block ms1 model buf (b :: bs) Hne] at hi
          exact hi

/-- The loop rule as a binary uses it: from the initial loop head with
an empty accumulator. -/
theorem rz_drain_top (segs : List Segment) (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Hcap_modeled : (cap : Int) ≤ rw_bytes_max)
    (LH : List byte → config → Prop) (Tfin : List byte → TSet)
    (Hfull : ∀ acc c, LH acc c → cap ≤ acc.length → realizes segs c (Tfin acc))
    (Hread : ∀ acc c, LH acc c → acc.length < cap →
      ∃ ms1 buf x8 w,
        m_halted (cfg_model c) = none ∧
        m_vm_lazy (cfg_model c) = [] ∧
        fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)) ∧
        msteps segs (cfg_ms c) ms1 ∧
        ms1.ms_svc_pending = some x8 ∧ bv_unsigned x8 = 63 ∧
        ms_gpr ms1 0 = Z_to_bv 64 0 ∧ ms_gpr ms1 1 = buf ∧
        ms_gpr ms1 2 = dcnt cap acc ∧
        read_bytes_map (ms_writable_byte segs ms1) buf (dcnt cap acc) = some w ∧
        access_okb buf (bv_unsigned (dcnt cap acc)) = true ∧
        realizes segs (rd_next ms1 (cfg_model c) buf []) (Tfin acc) ∧
        (∀ bs, rd_adm (m_stdin (cfg_model c)) (dcnt cap acc) bs → bs ≠ [] →
          LH (acc ++ bs) (rd_next ms1 (cfg_model c) buf bs)))
    (c : config) (H : LH [] c) :
    realizes segs c (t_drain cap Tfin cap (m_stdin (cfg_model c)) []) :=
  rz_drain segs cap Hcap Hcap_modeled LH Tfin Hfull Hread cap [] c (by omega) H

/-- An mmap whose failure arm is a binary's write-list-and-exit tail and
whose success arm reaches the drain loop head realizes the two-armed
shape. `mmap_model` rewrites only `vm_maps`, so the grant leaves the
remaining stdin, and hence the whole drain shape, untouched. -/
theorem rz_mmap_drain (segs : List Segment) (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Hcap_modeled : (cap : Int) ≤ rw_bytes_max)
    (LH : List byte → config → Prop) (Tfin : List byte → TSet)
    (Hfull : ∀ acc c, LH acc c → cap ≤ acc.length → realizes segs c (Tfin acc))
    (Hread : ∀ acc c, LH acc c → acc.length < cap →
      ∃ ms1 buf x8 w,
        m_halted (cfg_model c) = none ∧
        m_vm_lazy (cfg_model c) = [] ∧
        fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)) ∧
        msteps segs (cfg_ms c) ms1 ∧
        ms1.ms_svc_pending = some x8 ∧ bv_unsigned x8 = 63 ∧
        ms_gpr ms1 0 = Z_to_bv 64 0 ∧ ms_gpr ms1 1 = buf ∧
        ms_gpr ms1 2 = dcnt cap acc ∧
        read_bytes_map (ms_writable_byte segs ms1) buf (dcnt cap acc) = some w ∧
        access_okb buf (bv_unsigned (dcnt cap acc)) = true ∧
        realizes segs (rd_next ms1 (cfg_model c) buf []) (Tfin acc) ∧
        (∀ bs, rd_adm (m_stdin (cfg_model c)) (dcnt cap acc) bs → bs ≠ [] →
          LH (acc ++ bs) (rd_next ms1 (cfg_model c) buf bs)))
    (ms0 ms : machine_state) (model : Model) (x8 : word) (bf : List (List byte)) (cf : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model)
    (Hms : msteps segs ms0 ms) (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 222)
    (Hargs : mmap_args_ok ms)
    (Hfail : ∀ e, e ∈ mmap_errnos →
      to_wallexit segs (Z_to_bv 64 1) bf cf (advance_past_svc (set_gpr0 ms (errno_ret e))))
    (Hsucc : ∀ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true →
      LH [] (config.mkCfg
        (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
        (mmap_model a (page_round_up (ms_gpr ms 1)) model)))
    (Hex : ∃ a, grant_ok (ms_gpr ms 0) model a
      (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true)
    (Hbf : bufs_modeled bf) :
    realizes segs (config.mkCfg ms0 model)
      (t_alt2 (t_writes bf (t_exit cf (m_fs model)))
        (t_drain cap Tfin cap (m_stdin model) [])) := by
  apply rz_msteps segs ms0 ms model _ Hh Hlazy Hms
  apply rz_mmap segs ms model x8 _ _ Hh Hlazy Hsvc Hno Hargs ?_ ?_ Hex
  · intro e He
    exact wall_realizes segs _ model bf cf Hh Hlazy Hfd (Hfail e He) Hbf
  · intro a Ha
    exact rz_drain_top segs cap Hcap Hcap_modeled LH Tfin Hfull Hread _ (Hsucc a Ha)

theorem t_alt2_cong (A A' B B' : TSet) (HA : t_eq A A') (HB : t_eq B B') :
    t_eq (t_alt2 A B) (t_alt2 A' B') := by
  intro tr
  exact or_congr (HA tr) (HB tr)

/-- `rz_mmap_drain` with the drain collapsed: the first `cap` input bytes
as reads on channel 0, then the tail on those bytes. -/
theorem rz_mmap_drain_det (segs : List Segment) (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Hcap_modeled : (cap : Int) ≤ rw_bytes_max)
    (LH : List byte → config → Prop) (Tfin : List byte → TSet)
    (Htfin_ne : ∀ acc, Tfin acc [])
    (Hfull : ∀ acc c, LH acc c → cap ≤ acc.length → realizes segs c (Tfin acc))
    (Hread : ∀ acc c, LH acc c → acc.length < cap →
      ∃ ms1 buf x8 w,
        m_halted (cfg_model c) = none ∧
        m_vm_lazy (cfg_model c) = [] ∧
        fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)) ∧
        msteps segs (cfg_ms c) ms1 ∧
        ms1.ms_svc_pending = some x8 ∧ bv_unsigned x8 = 63 ∧
        ms_gpr ms1 0 = Z_to_bv 64 0 ∧ ms_gpr ms1 1 = buf ∧
        ms_gpr ms1 2 = dcnt cap acc ∧
        read_bytes_map (ms_writable_byte segs ms1) buf (dcnt cap acc) = some w ∧
        access_okb buf (bv_unsigned (dcnt cap acc)) = true ∧
        realizes segs (rd_next ms1 (cfg_model c) buf []) (Tfin acc) ∧
        (∀ bs, rd_adm (m_stdin (cfg_model c)) (dcnt cap acc) bs → bs ≠ [] →
          LH (acc ++ bs) (rd_next ms1 (cfg_model c) buf bs)))
    (ms0 ms : machine_state) (model : Model) (x8 : word) (bf : List (List byte)) (cf : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model)
    (Hms : msteps segs ms0 ms) (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 222)
    (Hargs : mmap_args_ok ms)
    (Hfail : ∀ e, e ∈ mmap_errnos →
      to_wallexit segs (Z_to_bv 64 1) bf cf (advance_past_svc (set_gpr0 ms (errno_ret e))))
    (Hsucc : ∀ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true →
      LH [] (config.mkCfg
        (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
        (mmap_model a (page_round_up (ms_gpr ms 1)) model)))
    (Hex : ∃ a, grant_ok (ms_gpr ms 0) model a
      (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true)
    (Hbf : bufs_modeled bf) :
    realizes segs (config.mkCfg ms0 model)
      (t_alt2 (t_writes bf (t_exit cf (m_fs model)))
        (t_emit ((stream_firstn (m_stdin model) cap).map (ReadEv (Z_to_bv 64 0)))
          (Tfin (stream_firstn (m_stdin model) cap)))) := by
  refine realizes.rz_conseq (config.mkCfg ms0 model) _ _
    (rz_mmap_drain segs cap Hcap Hcap_modeled LH Tfin Hfull Hread
      ms0 ms model x8 bf cf Hh Hlazy Hfd Hms Hsvc Hno Hargs Hfail Hsucc Hex Hbf) ?_
  exact t_alt2_cong _ _ _ _ (t_eq_refl _)
    (t_drain_top_collapse cap Hcap Tfin Htfin_ne (m_stdin model))

end LinuxProcessSemantics.Common.DrainAlg
