import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.StepTac

/-! rocq-baseline: 2cde689f94c086b868999970834b76a25616b94a -/

/-! # Common.ArgvEnv — parametric argv/envp/stack-window startup scaffolding

Ported from `theories/Common/ArgvEnv.v` at the baseline above, with the
Rocq names and statements: the sp-window restatements, the argument count
`argcN`, the stack-image no-overflow bound `bsb_nw`, musl's `environ` value
`envp_ptr`, the `k`-th argv pointer's address bounds `argv_ptr_bounds_at`,
and the wrapped initial memory `wmem` with its read-backs of the argc word
and of the `k`-th argv pointer.  Why this bookkeeping is proved
once here, and what cannot live here (the per-binary overlay peels), is the
Rocq file's header, not repeated here.  That header's three statements of
what the bookkeeping depends on (its lines 3-8 and 13-14) leave out `ph`,
`uid`, `hw` and `rnd`, and two of them leave out `segs` as well; the first
bullet below names all eight variables.

Spellings that differ:
- Rocq's section `Scaffold` quantifies over `segs ph sp av ev uid hw rnd`
  and the hypotheses `Hva Hve Hsp_lo Hsp_hi`; each Lean constant takes, as
  explicit leading arguments in Rocq's discharge order, exactly the ones
  the Rocq constant is discharged over, so `k` and `a n` follow them.
- Rocq's `nth k av []` is `av.getD k []`, and `Z.of_nat` is the
  `Nat`-to-`Int` cast. -/

namespace LinuxProcessSemantics.Common.ArgvEnv

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.StepTac

/-! ## sp-window bounds (per-example Rocq `rsp_lo_num`/`rsp_hi_num`/`asp_*`, over any `sp`) -/

theorem sp_lo_num (sp : word) (hsp_lo : sp_window_lo ≤ bv_unsigned sp) :
    0x7fff80000000 ≤ bv_unsigned sp :=
  hsp_lo

theorem sp_hi_num (sp : word) (hsp_hi : bv_unsigned sp ≤ sp_window_hi) :
    bv_unsigned sp ≤ 0x800000000000 :=
  hsp_hi

/-! ## argc -/

def argcN (av : List (List byte)) : word := len_word av

theorem u_argcN (av : List (List byte)) (hva : valid_argv av) :
    bv_unsigned (argcN av) = (av.length : Int) := by
  have h := valid_argv_len av hva
  unfold argcN len_word
  exact u_Z2bv _ (Int.natCast_nonneg _) (by omega)

/-! ## No-overflow bound for the initial stack image -/

theorem bsb_nw (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (uid hw : word)
    (rnd : EntryDraw) (hva : valid_argv av) (hve : valid_envp ev)
    (hsp_hi : bv_unsigned sp ≤ sp_window_hi) :
    bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64 := by
  have h1 := bsb_bound ph sp av ev uid hw rnd hva hve
  have h2 := sp_hi_num sp hsp_hi
  omega

/-! ## envp pointer (the value _start stores into musl's environ slot) -/

def envp_ptr (sp : word) (av : List (List byte)) : word :=
  Z_to_bv 64 (bv_unsigned sp + 8 + 8 * (av.length : Int) + 8)

theorem envp_ptr_eq (sp : word) (av : List (List byte)) (hva : valid_argv av)
    (hsp_lo : sp_window_lo ≤ bv_unsigned sp) (hsp_hi : bv_unsigned sp ≤ sp_window_hi) :
    v_addi (v_add (Z_to_bv 64 (bv_unsigned sp + 8)) (v_slli (argcN av) 3)) 8 = envp_ptr sp av := by
  have h1 := sp_hi_num sp hsp_hi
  have h2 := sp_lo_num sp hsp_lo
  have hlen := valid_argv_len av hva
  have hs8 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 8)) = bv_unsigned sp + 8 :=
    u_Z2bv _ (by omega) (by omega)
  have hsl : bv_unsigned (v_slli (argcN av) 3) = 8 * (av.length : Int) := by
    rw [v_slli_3 _ (by rw [u_argcN av hva]; omega), u_argcN av hva]
  apply bv_eq_of_unsigned
  unfold envp_ptr v_addi
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, v_add_small _ _ (by rw [hs8, hsl]; omega), hs8, hsl]

/-! ## Wrapped initial memory and its read-backs -/

def wmem (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (uid hw : word)
    (rnd : EntryDraw) : word → Option byte :=
  wrap_mem ph sp av ev uid hw rnd

/-- At/above `sp` the wrapper equals the raw stack image (peels the
zero-fill branch); this is the shared, overlay-free member of the
`rdn_<layer>_above`/`rdn_wmem_stack` peeling triad. -/
theorem rdn_wmem_stack (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (av ev : List (List byte)) (uid hw : word) (rnd : EntryDraw) (a : word) (n : Nat)
    (ha : bv_unsigned sp ≤ bv_unsigned a) (hn : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn segs (wmem ph sp av ev uid hw rnd) a n =
      rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd)) a n :=
  rdn_wrap_stack_above segs ph sp av ev a n uid hw rnd ha hn

/-- The argc word at `sp`. -/
theorem read_argc_w (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (av ev : List (List byte)) (uid hw : word) (rnd : EntryDraw) (hva : valid_argv av)
    (hve : valid_envp ev) (hsp_hi : bv_unsigned sp ≤ sp_window_hi) :
    rdn segs (wmem ph sp av ev uid hw rnd) sp 8 = some (word_le8 (argcN av)) := by
  have h1 := sp_hi_num sp hsp_hi
  rw [rdn_wmem_stack segs ph sp av ev uid hw rnd sp 8 (Int.le_refl _) (by omega)]
  exact read_argc ph segs sp av ev uid hw rnd (bsb_nw ph sp av ev uid hw rnd hva hve hsp_hi)

/-! ## argv-pointer group (pointer bounds + read-back of the pointer word through `wmem`) -/

/-- Address bounds for the `k`-th argv pointer.  Generalizes the
per-example `psrc_bounds`/`pdst_bounds` over the index `k`; note it is
`segs`- and overlay-independent. -/
theorem argv_ptr_bounds_at (sp : word) (av ev : List (List byte)) (hva : valid_argv av)
    (hve : valid_envp ev) (hsp_hi : bv_unsigned sp ≤ sp_window_hi) (k : Nat)
    (hk : k < av.length) :
    bv_unsigned sp ≤ bv_unsigned (cat_argv_ptr sp av ev k) ∧
      bv_unsigned (cat_argv_ptr sp av ev k) + ((av.getD k []).length : Int) + 1 < 2 ^ 64 := by
  apply argv_ptr_bounds sp av ev k hva hve hk
  have h1 := sp_hi_num sp hsp_hi
  unfold argv_layout_slack
  omega

/-- Read-back of the `k`-th argv pointer word out of `wmem` (the
overlay-free tail the `read_psrc_*`/`read_pdst_*` lemmas reduce to after
peeling their own overlay). -/
theorem read_argv_ptr_w (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (av ev : List (List byte)) (uid hw : word) (rnd : EntryDraw) (hva : valid_argv av)
    (hve : valid_envp ev) (hsp_lo : sp_window_lo ≤ bv_unsigned sp)
    (hsp_hi : bv_unsigned sp ≤ sp_window_hi) (k : Nat) (hk : k < av.length) :
    rdn segs (wmem ph sp av ev uid hw rnd) (sp + nat_to_word (8 + 8 * k)) 8 =
      some (word_le8 (cat_argv_ptr sp av ev k)) := by
  have h1 := sp_lo_num sp hsp_lo
  have h2 := sp_hi_num sp hsp_hi
  have hal := valid_argv_len av hva
  have hu : bv_unsigned (sp + nat_to_word (8 + 8 * k)) =
      bv_unsigned sp + ((8 + 8 * k : Nat) : Int) := by
    rw [word_add_nat]
    exact u_Z2bv _ (by omega) (by omega)
  rw [rdn_wmem_stack segs ph sp av ev uid hw rnd _ 8 (by rw [hu]; omega) (by rw [hu]; omega)]
  exact read_argv_ptr_k ph segs sp av ev k uid hw rnd hk
    (bsb_nw ph sp av ev uid hw rnd hva hve hsp_hi)

end LinuxProcessSemantics.Common.ArgvEnv
