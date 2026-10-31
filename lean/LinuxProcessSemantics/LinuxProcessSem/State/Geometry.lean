-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/State.v
import LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! rocq-baseline: 7b4cf49586658ecbffbab14145ab0969272a0b23 -/

/-! # LinuxProcessSem.State.Geometry — the address-space constants

One part of `State.v`'s twin, re-exported by `State.lean`, whose header
says how the ten parts divide the Rocq file, what a part may hold and
where the pins live.

WHAT GOES HERE: the constants of the address-space geometry, each
argued on its Rocq definition — the page size, the stack limit, the
entry-sp and `mmap_base` windows, `TASK_SIZE` and the declared
address-space size `VaSize` with its per-depth constants, `2^64`, the
per-role backing budgets — and `addr_is_error_b`, the errno window
test over `two_pow_64`, which Rocq keeps with these constants.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.State

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! ## Constants (the address-space geometry, each argued in Rocq) -/

def page_size : Int := 4096

def page_round_up_Z (n : Int) : Int := ((n + page_size - 1) / page_size) * page_size
def page_round_down_Z (n : Int) : Int := (n / page_size) * page_size

/-- Rounding a positive length up reaches at least one page: the length
the allocator charges for a nonempty request is never zero.
Rocq: `State.page_round_up_Z_pos`. -/
theorem page_round_up_Z_pos (n : Int) (hn : 0 < n) : page_size ≤ page_round_up_Z n := by
  unfold page_round_up_Z page_size
  omega

/-- RLIMIT_STACK's soft limit: the zero-mapped window below the entry sp. -/
def stack_max_size : Int := 8 * 1024 * 1024

/-- The entry stack pointer's window (riscv64 Sv48/Sv57 STACK_TOP and the
stack ASLR band below it; the derivation is on the Rocq constants). -/
def sp_window_lo : Int := 0x7fff80000000
def sp_window_hi : Int := 0x800000000000

/-- The break's image-relative ASLR band: the kernel's own reach, one
page above the page-rounded image top plus a page-multiple displacement
of at most 1 GiB less one page (`arch_randomize_brk` ->
`randomize_page(_, SZ_1G)`, mm/util.c, read in Linux v6.12.1).  The two
cancel, so the reach is exactly 1 GiB and is attained.  The derivation,
and why a wider band was wrong, are on the Rocq constant. -/
def brk_aslr_max : Int := 1 * 1024 * 1024 * 1024

/-- The `mm->mmap_base` band. -/
def mmap_base_min : Int := 0x154555557000
def mmap_base_max : Int := sp_window_hi - 128 * 1024 * 1024

def TASK_SIZE : Int := 0x800000000000

/-- The address-space size as a declared parameter of the run: the
page-table depth the kernel booted with.  `va_task_size` is
`TASK_SIZE_64` per depth and `va_stack_top` is `STACK_TOP`, which is
capped at 2^47 (`MMAP_VA_BITS_64`, arch/riscv/include/asm/pgtable.h;
arch/riscv/include/asm/processor.h, Linux v6.18.46, commit
1f99e9ab748f), so Sv48 and Sv57 share it.  The derivations and the
Sv39 floor argument are on the Rocq definitions. -/
inductive VaSize where
  | Sv39 | Sv48 | Sv57
  deriving DecidableEq, Repr

def sv39_task_size : Int := 0x4000000000
def sv57_task_size : Int := 0x100000000000000

def va_task_size (v : VaSize) : Int :=
  match v with
  | .Sv39 => sv39_task_size
  | .Sv48 => TASK_SIZE
  | .Sv57 => sv57_task_size

def va_stack_top (v : VaSize) : Int :=
  match v with
  | .Sv39 => sv39_task_size
  | .Sv48 => sp_window_hi
  | .Sv57 => sp_window_hi

def va_sp_window_hi (v : VaSize) : Int := va_stack_top v
def va_sp_window_lo (v : VaSize) : Int := va_stack_top v - 2 * 1024 * 1024 * 1024
def va_mmap_base_max (v : VaSize) : Int := va_stack_top v - 128 * 1024 * 1024
def va_mmap_base_min (v : VaSize) : Int :=
  match v with
  | .Sv39 => 0
  | .Sv48 => mmap_base_min
  | .Sv57 => mmap_base_min

/-- `2^64`, the bound every range check in `Int` compares against. -/
def two_pow_64 : Int := 2 ^ 64

/-- The per-role backed anonymous-memory budgets. -/
def source_alloc_limit : Int := 0x400000000     -- 16 GiB
def target_alloc_limit : Int := 0x8000000000    -- 512 GiB

/-- a0 encodes a kernel error iff it is `-errno` for errno in `[1, 4095]`:
`IS_ERR_VALUE` is `(unsigned long)(x) >= (unsigned long)-MAX_ERRNO` with
`MAX_ERRNO` 4095 (include/linux/err.h, v6.18.46). -/
def addr_is_error_b (ret : word) : Bool :=
  two_pow_64 - 4096 < bv_unsigned ret

end LinuxProcessSemantics.LinuxProcessSem.State
