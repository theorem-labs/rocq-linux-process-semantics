import LinuxProcessSemantics.Common.CatExec

/-! Not part of the trusted specification.

CatExec.v defines no Ltac tactics. These applications pin the argument order
and statement shapes used by the example proofs, including the terminating
NUL and the strict lower bound of the stack window. -/

namespace LinuxProcessSemantics.Common.CatExecTests

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec

example (s : List byte) : byte_at s s.length = Z_to_bv 8 0 := byte_at_len s

example (s : List byte) (j : Nat) (hnz : ¬ Z_to_bv 8 0 ∈ s) (hj : j < s.length) :
    byte_at s j ≠ Z_to_bv 8 0 := byte_at_nz s j hnz hj

example (ph : PhdrInfo) (segs : List Segment) (sp : word) (av ev : List (List byte))
    (k j : Nat) (uid hw : word) (rnd : EntryDraw)
    (hk : k < av.length) (hj : j ≤ (av.getD k []).length)
    (hnw : bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
        (cat_argv_ptr sp av ev k + nat_to_word j) 1 =
      some [(av.getD k [] ++ [Z_to_bv 8 0]).getD j (Z_to_bv 8 0)] :=
  read_argv_byte_k ph segs sp av ev k j uid hw rnd hk hj hnw

example (ph : PhdrInfo) (segs : List Segment) (sp : word) (av ev : List (List byte))
    (k : Nat) (uid hw : word) (rnd : EntryDraw) (hk : k < av.length)
    (hnw : bv_unsigned sp + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
        (cat_argv_ptr sp av ev k) (av.getD k []).length = some (av.getD k []) :=
  read_argv_str_k ph segs sp av ev k uid hw rnd hk hnw

example : stack_max_size = 8388608 := stack_max_size_val

example (ph : PhdrInfo) (sp : word) (argv envp : List (List byte)) (addr uid hw : word)
    (rnd : EntryDraw) (hlt : bv_unsigned addr < bv_unsigned sp - stack_max_size) :
    wrap_mem ph sp argv envp uid hw rnd addr = none :=
  wrap_mem_below ph sp argv envp addr uid hw rnd hlt

example : byte_at [Z_to_bv 8 65] 0 = Z_to_bv 8 65 := rfl

example : ¬ byte_at [Z_to_bv 8 65] 1 ≠ Z_to_bv 8 0 :=
  fun h => h (byte_at_len [Z_to_bv 8 65])

example (ph : PhdrInfo) (argv envp : List (List byte)) (uid hw : word) (rnd : EntryDraw) :
    wrap_mem ph (Z_to_bv 64 8388608) argv envp uid hw rnd 0 = some 0 := by
  rfl

example (ph : PhdrInfo) (argv envp : List (List byte)) (uid hw : word) (rnd : EntryDraw) :
    wrap_mem ph (Z_to_bv 64 8388608) argv envp uid hw rnd 0 ≠ none := by
  exact Option.some_ne_none 0

example : v_addi ((Z_to_bv 64 (-1)) + 1) (-1) = Z_to_bv 64 (-1) :=
  v_addi_pred (Z_to_bv 64 (-1))

end LinuxProcessSemantics.Common.CatExecTests
