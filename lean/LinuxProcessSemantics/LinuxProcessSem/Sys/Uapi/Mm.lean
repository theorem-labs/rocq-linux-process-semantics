import LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Uapi.Mm — the memory-mapping ABI constants

One part of `theories/LinuxProcessSem/Sys/Uapi.v` (see `Sys/Uapi.lean`
for the split).  WHAT GOES HERE: the `PROT_`, `MAP_`, `MREMAP_` and
`MADV_` words of mmap, mprotect, mremap and madvise.

TRUST BOUNDARY: this file is part of the trusted specification.

riscv64 carries no arch/riscv/include/uapi/asm/mman.h of its own, so the
arch-generic headers are its ABI.  Rocq read the `PROT_`/`MAP_` block and
`MREMAP_MAYMOVE` at v6.12 and the other two at v6.18.46; the line numbers
below are Linux v6.18.46's, commit
1f99e9ab748fc5c32120de9c4eca31abfe54a4d5, where every value is the
same. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- `#define PROT_READ 0x1` (include/uapi/asm-generic/mman-common.h:10,
Linux v6.18.46, commit 1f99e9ab748f). -/
def PROT_READ : Int := 1

/-- `#define PROT_WRITE 0x2` (include/uapi/asm-generic/mman-common.h:11,
Linux v6.18.46, commit 1f99e9ab748f). -/
def PROT_WRITE : Int := 2

/-- `#define PROT_NONE 0x0` (include/uapi/asm-generic/mman-common.h:16,
Linux v6.18.46, commit 1f99e9ab748f). -/
def PROT_NONE : Int := 0

/-- `#define PROT_GROWSDOWN 0x01000000`
(include/uapi/asm-generic/mman-common.h:17, Linux v6.18.46, commit
1f99e9ab748f).  Not a permission: `do_mprotect_pkey` (mm/mprotect.c,
Linux v6.18.46) masks it and `PROT_GROWSUP` out of `prot` before
anything else looks at it, and only their conjunction is an argument
error (`Mprotect.mprotect_grows_conflict_b`). -/
def PROT_GROWSDOWN : Int := 0x01000000

/-- `#define PROT_GROWSUP 0x02000000`
(include/uapi/asm-generic/mman-common.h:18, Linux v6.18.46, commit
1f99e9ab748f); see `PROT_GROWSDOWN`. -/
def PROT_GROWSUP : Int := 0x02000000

/-- `#define MAP_PRIVATE 0x02` (include/uapi/linux/mman.h:18, Linux
v6.18.46, commit 1f99e9ab748f).  Rocq cites the whole `PROT_`/`MAP_`
block to include/uapi/asm-generic/mman-common.h at v6.12; this one
define is the exception, and sits in include/uapi/linux/mman.h at v6.12
too (line 18 there as well). -/
def MAP_PRIVATE : Int := 2

/-- `#define MAP_FIXED 0x10` (include/uapi/asm-generic/mman-common.h:22,
Linux v6.18.46, commit 1f99e9ab748f). -/
def MAP_FIXED : Int := 16

/-- `#define MAP_ANONYMOUS 0x20` (include/uapi/asm-generic/mman-common.h:23,
Linux v6.18.46, commit 1f99e9ab748f). -/
def MAP_ANONYMOUS : Int := 32

/-- `#define MAP_HUGETLB 0x040000` (include/uapi/asm-generic/mman-common.h:29,
Linux v6.18.46, commit 1f99e9ab748f). -/
def MAP_HUGETLB : Int := 262144

/-- `#define MAP_FIXED_NOREPLACE 0x100000`
(include/uapi/asm-generic/mman-common.h:31, Linux v6.18.46, commit
1f99e9ab748f).  Placement at `addr` exactly, as MAP_FIXED, but a refusal
rather than a replacement when any page of the range is already mapped;
`do_mmap` (mm/mmap.c, Linux v6.18.46) is where both halves are decided,
and `Mmap.mmap_noreplace_flags_b` carries the reading. -/
def MAP_FIXED_NOREPLACE : Int := 1048576

/-- `#define MREMAP_MAYMOVE 1` (include/uapi/linux/mman.h:9, Linux
v6.18.46, commit 1f99e9ab748f; Rocq read the same line at v6.12).
Architecture-independent: neither include/uapi/asm-generic/mman.h nor
mman-common.h redefines any `MREMAP_` bit, so this uapi header is the
sole definition. -/
def MREMAP_MAYMOVE : Int := 1

/-- `#define MADV_DONTNEED 4` (include/uapi/asm-generic/mman-common.h:49,
Linux v6.18.46, commit 1f99e9ab748f).  Architecture-independent for the
reason `MREMAP_MAYMOVE` is: the arch-generic mman.h defines no `MADV_`
value.  `Mm.Madvise.madvise_dontneed_b` is the one reader. -/
def MADV_DONTNEED : Int := 4

end LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
