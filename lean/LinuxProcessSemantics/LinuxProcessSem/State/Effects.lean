import LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! rocq-baseline: 7b4cf49586658ecbffbab14145ab0969272a0b23 -/

/-! # LinuxProcessSem.State.Effects — syscall inputs and effects

One part of `State.v`'s twin, re-exported by `State.lean`, whose header
says how the ten parts divide the Rocq file, what a part may hold and
where the pins live.

WHAT GOES HERE: what a syscall is handed (`SyscallInput`) and what it
does to the machine (`SyscallEffect`, `MemCopy`), with `mkEffect`,
the constructor specs build effects through, and `with_copyins`.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.State

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! ## Syscall inputs and effects -/

structure SyscallInput where
  mkInput ::
  in_sysno : word               -- a7 at ecall
  in_args  : List word          -- a0..a5 at ecall
  in_mem   : word → Option byte -- pre-syscall memory (writable merged over ROM)
  in_wmem  : word → Option byte -- the WRITABLE view (copy_to_user's EFAULT gate)

def in_arg (i : SyscallInput) (k : Nat) : word :=
  i.in_args.getD k (Z_to_bv 64 0)

/-- One symbolic memory copy. -/
structure MemCopy where
  mkCopy ::
  copy_src : word
  copy_dst : word
  copy_len : word

/-- What a syscall does to the machine.  See the Rocq header for the
order `Run.apply_effect` applies the five ledgers in. -/
structure SyscallEffect where
  mkEffectU ::
  eff_ret    : word
  eff_writes : List (word × List byte)  -- (base address, bytes), applied in order
  eff_zeros  : List (word × word)       -- (base address, size) zero-filled ranges
  eff_unmaps : List (word × word)       -- (base address, size) unmapped ranges
  eff_copies : List MemCopy             -- pre-effect (source, destination, size) copies
  eff_copyins : List (word × Nat)       -- ranges already read from user memory

/-- The common no-unmap/no-copy/no-copyin convenience. -/
abbrev mkEffect (r : word) (ws : List (word × List byte)) (zs : List (word × word)) : SyscallEffect :=
  SyscallEffect.mkEffectU r ws zs [] [] []

def with_copyins (reads : List (word × Nat)) (eff : SyscallEffect) : SyscallEffect :=
  SyscallEffect.mkEffectU eff.eff_ret eff.eff_writes eff.eff_zeros
    eff.eff_unmaps eff.eff_copies reads

end LinuxProcessSemantics.LinuxProcessSem.State
