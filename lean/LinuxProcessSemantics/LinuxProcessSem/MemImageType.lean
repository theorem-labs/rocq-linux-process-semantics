import LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! # MemImageType — shared types for memory image snapshots

Mirrors `theories/LinuxProcessSem/MemImageType.v`.

TRUST BOUNDARY: this file is part of the trusted specification.

Defines the `Segment` record used by all generated MemImage files and by
`RiscvSemantics` for memory reads.  Rocq keeps segment bytes as
`PrimString` hex chunks read through the `rocq-read-file` plugin; here
they are Lean `String`s with the same content (lowercase hex, no spaces),
so a snapshot file transcribes verbatim.  `N` is `Nat`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.MemImageType

structure Segment where
  seg_base  : Nat
  seg_size  : Nat
  seg_perms : String
  seg_bytes : List String  -- hex chunks, lowercase, no spaces

/-- Where the binary's PROGRAM HEADER TABLE lands in memory, published to
the process through AT_PHDR/AT_PHENT/AT_PHNUM (see the Rocq file for why a
static libc needs it: `__init_tls` walks it to find PT_TLS). -/
structure PhdrInfo where
  mkPhdrInfo ::
  ph_addr : Nat   -- AT_PHDR  — run-time address of the phdr table
  ph_ent  : Nat   -- AT_PHENT — e_phentsize (56 on ELF64)
  ph_num  : Nat   -- AT_PHNUM — e_phnum

/-- Does the permission string carry the flag character `c`?  The three
flag letters are distinct and appear nowhere else in the string. -/
def string_has (c : Char) (s : String) : Bool :=
  s.toList.any (fun c' => c' == c)

def seg_readable   (seg : Segment) : Bool := string_has 'r' seg.seg_perms
def seg_writable   (seg : Segment) : Bool := string_has 'w' seg.seg_perms
def seg_executable (seg : Segment) : Bool := string_has 'x' seg.seg_perms

/-- The data a single compiled binary contributes to the model, as a
RECORD (Rocq also has the `MemImage` module type the generated snapshot
files implement; the record is what `Run.run` and the statements take). -/
structure Image where
  mkImage ::
  img_segments : List Segment
  img_init_pc  : Nat
  img_phdrs    : PhdrInfo

end LinuxProcessSemantics.LinuxProcessSem.MemImageType
