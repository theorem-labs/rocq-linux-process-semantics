import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! # Checks.Cases.Sys.Uapi.Mm — the `Sys.Uapi.Mm` constants, read off
against Linux

Pins over `Sys/Uapi/Mm.lean`, the memory-mapping words. Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about a header or a function of
Linux v6.18.46, commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5, with the
citation beside it.

Each pin states a value the kernel really has and, beside it, refutes the
concrete mistake the constant exists to prevent — a value from another
architecture's header, an off-by-one at a bound, a decimal read of an
octal, a mask taken for its neighbour.  They are stated about the cited
headers and sources, never about the Rocq definitions of the same names.
No Rocq file sits at this file's mirror path: the Rocq tree keeps its
Uapi constants unpinned (this stops being true the day a Rocq case
file pins them), so this file is the Lean port's own evidence rather
than a twin. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Mm

open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- The `PROT_` words (include/uapi/asm-generic/mman-common.h:10-18).  The
two `GROWS` modifiers share no bit with the three permissions, which is
what lets `do_mprotect_pkey` (mm/mprotect.c, Linux v6.18.46) mask them
off before it reads `prot` as permissions. -/
theorem prot_words :
    PROT_NONE = 0 ∧ PROT_READ = 1 ∧ PROT_WRITE = 2
    ∧ PROT_GROWSDOWN = 0x01000000 ∧ PROT_GROWSUP = 0x02000000
    ∧ PROT_GROWSDOWN ≠ PROT_GROWSUP
    ∧ (PROT_GROWSDOWN.toNat &&& 7 : Nat) = 0 ∧ (PROT_GROWSUP.toNat &&& 7 : Nat) = 0 := by decide

/-- The `MAP_` words (include/uapi/linux/mman.h:18 and
include/uapi/asm-generic/mman-common.h:22-31, Linux v6.18.46).
`MAP_FIXED_NOREPLACE` is
an INDEPENDENT bit, not `MAP_FIXED` plus one: a NOREPLACE request arrives
with `MAP_FIXED` clear, and `do_mmap` (mm/mmap.c, Linux v6.18.46) tests
the two separately, so a model reading NOREPLACE as a flavour of FIXED
would replace the mapping Linux refuses to touch.  `MAP_ANONYMOUS` is
0x20, not mips's 0x0800 (arch/mips/include/uapi/asm/mman.h:42). -/
theorem map_words :
    MAP_PRIVATE = 2 ∧ MAP_FIXED = 0x10 ∧ MAP_ANONYMOUS = 0x20 ∧ MAP_HUGETLB = 0x40000
    ∧ MAP_FIXED_NOREPLACE = 0x100000
    ∧ (MAP_FIXED_NOREPLACE.toNat &&& MAP_FIXED.toNat : Nat) = 0
    ∧ MAP_ANONYMOUS ≠ 0x800 := by decide

/-- `MREMAP_MAYMOVE` is 1 (include/uapi/linux/mman.h:9, Linux v6.18.46); 2 is
`MREMAP_FIXED` (line 10), which needs a fifth argument and no arm reads.
`MADV_DONTNEED` is 4 (include/uapi/asm-generic/mman-common.h:49, Linux
v6.18.46); 8 is `MADV_FREE` (line 52), which keeps the pages until memory pressure and would make a
"discard now" model wrong about what a later read returns. -/
theorem mremap_and_madvise_words :
    MREMAP_MAYMOVE = 1 ∧ MREMAP_MAYMOVE ≠ 2 ∧ MADV_DONTNEED = 4 ∧ MADV_DONTNEED ≠ 8 := by
  decide

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Mm
