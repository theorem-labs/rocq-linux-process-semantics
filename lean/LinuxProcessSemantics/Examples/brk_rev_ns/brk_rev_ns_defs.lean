import LinuxProcessSemantics.Common.AllocSim
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.ListFacts

/-! rocq-baseline: 3bd94f932fe0933df59ec88e6cc87819fee0d9d1 -/

/-! # brk-rev-ns: shared definitions and helper lemmas.

PROOF-SIDE FILE (not part of the trusted specification).

The shared observable-behavior spec of both binaries:
- argc < 2                    : no output, exit 2
- n = strlen(argv[1]) > 65536 : no output, exit 3
- otherwise                   : the outcome SET
    { ([], 4) } ∪ { ([rev_buf argv[1]], 0) }
  (brk resolutions: any failing resolution exits 4 silently; any
  succeeding resolution writes the reversed string + '\n' and exits 0;
  both kinds of resolution always exist).

This file: the outcome-set definitions and the resolution-set algebra
shared by the two per-binary proofs, plus argv/byte helpers and word
bridges for the down-counting loops.

Conventions: bytes are `byte = BitVec 8`, machine values `word = BitVec 64`;
unbounded bookkeeping is in `Int` over `bv_unsigned`; computed stack
addresses use the canonical `Z_to_bv 64 (...)` form; loop indices/counters
use `nat_to_word`.
-/

namespace LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_defs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.Common
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Common.AllocSim

/-- The single written buffer on a successful run: argv[1] reversed,
    then a newline. -/
def rev_buf (s : List byte) : List byte := s.reverse ++ [Z_to_bv 8 10]

/-- The shared outcome set for the main (argc >= 2, n <= 65536) case. -/
def brkU (wbuf : List byte) : (List (List byte) × word) → Prop :=
  fun o => o = ([], Z_to_bv 64 4) ∨ o = ([wbuf], Z_to_bv 64 0)

/-- Loop-index steps over a symbolic base (both sides wrap). -/
theorem nat_to_word_S (m : Nat) :
    v_addi (nat_to_word m) 1 = nat_to_word (Nat.succ m) := by
  apply bv_eq_of_unsigned
  simp only [v_addi, nat_to_word, Z_to_bv_unsigned, bv_wrap64_mod,
    Int.emod_add_emod, Int.natCast_succ]

/-- The first brk node: brk(0) is DETERMINISTIC — it reports the
    quantified ASLR base `b` (`Run.mi_init_brk`, established at execve) —
    so the resolution set is the singleton {b}, and the branch outcome
    set is `T1` AT `b`. `growable` at `b` (from `Run.valid_brk`'s window
    bounds) makes both outcomes live: the second brk's failure resolution
    exits 4, its success resolution writes and exits 0. -/
theorem brkU_iff_T1 (reserved : List (word × word)) (lim top : Int) (n : word)
    (wbuf : List byte) (b : word) (P : word → Prop)
    (HP : ∀ r, P r ↔ r = b)
    (Hg : growable reserved lim top (n + 1) b)
    (Hn1 : n + 1 ≠ Z_to_bv 64 0) :
    ∀ o, brkU wbuf o ↔ ∃ r, P r ∧ T1 reserved lim top (n + 1) [wbuf] r o := by
  intro o
  constructor
  · intro h
    rcases h with h | h
    · exact ⟨b, (HP b).mpr rfl, Or.inl ⟨h, Or.inr (Or.inr Hn1)⟩⟩
    · exact ⟨b, (HP b).mpr rfl, Or.inr ⟨Hg, h⟩⟩
  · rintro ⟨r, _, h⟩
    rcases h with ⟨ho, _⟩ | ⟨_, ho⟩
    · exact Or.inl ho
    · exact Or.inr ho

theorem length_rev_buf (s : List byte) : (rev_buf s).length = Nat.succ s.length := by
  simp only [rev_buf, List.length_append, List.length_reverse, List.length_cons,
    List.length_nil, Nat.succ_eq_add_one]

theorem nth_rev_lt (s : List byte) (i : Nat) (Hi : i < s.length) :
    s.reverse.getD i (Z_to_bv 8 0) = s.getD (s.length - Nat.succ i) (Z_to_bv 8 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_reverse Hi]
  rw [show s.length - 1 - i = s.length - Nat.succ i by omega]

theorem firstn_rev_snoc (s : List byte) (i : Nat) (Hi : i < s.length) :
    s.reverse.take (Nat.succ i) =
      s.reverse.take i ++ [s.getD (s.length - Nat.succ i) (Z_to_bv 8 0)] := by
  have Hi' : i < s.reverse.length := by rw [List.length_reverse]; exact Hi
  rw [ListFacts.firstn_S_nth byte s.reverse i (Z_to_bv 8 0) Hi', nth_rev_lt s i Hi]

theorem firstn_all_rev (s : List byte) : s.reverse.take s.length = s.reverse := by
  rw [← List.length_reverse (as := s)]
  exact ListFacts.firstn_all_len s.reverse

end LinuxProcessSemantics.Examples.brk_rev_ns.brk_rev_ns_defs
