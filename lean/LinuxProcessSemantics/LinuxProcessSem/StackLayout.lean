import LinuxProcessSemantics.LinuxProcessSem.MemImageType

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # StackLayout — Linux process initial stack builder

Mirrors `theories/LinuxProcessSem/StackLayout.v`.

TRUST BOUNDARY: this file is part of the trusted specification.

Builds the byte sequence the kernel places on the stack at process
startup: argc, argv pointers, envp pointers, auxiliary vector, and
null-terminated string data.  The auxv's entry set and the reason each
entry is there (or absent: AT_GID/AT_EGID, …) are argued on the
Rocq definition, against `create_elf_tables` (fs/binfmt_elf.c, Linux
v6.18.46, commit 1f99e9ab748f). -/

namespace LinuxProcessSemantics.LinuxProcessSem.StackLayout

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType

def string_addrs (base : word) (strs : List (List byte)) : List word × word :=
  match strs with
  | [] => ([], base)
  | s :: rest =>
    let next := base + len_word s + 1
    let (ptrs, final) := string_addrs next rest
    (base :: ptrs, final)

def flatten_strings (strs : List (List byte)) : List byte :=
  strs.flatMap (fun s => s ++ [Z_to_bv 8 0])

def AT_NULL    : word := Z_to_bv 64 0
def AT_PHDR    : word := Z_to_bv 64 3
def AT_PHENT   : word := Z_to_bv 64 4
def AT_PHNUM   : word := Z_to_bv 64 5
def AT_PAGESZ  : word := Z_to_bv 64 6
def AT_UID     : word := Z_to_bv 64 11
def AT_EUID    : word := Z_to_bv 64 12
def AT_HWCAP   : word := Z_to_bv 64 16
def AT_SECURE  : word := Z_to_bv 64 23
def AT_RANDOM  : word := Z_to_bv 64 25

/-- Port of `StackLayout.v` at reference commit
7f386a77d4d3877f162c91f06b7e4fcc1d998e61. Its AT_HWCAP argument traces
these masks and their validity domain to the pinned implementation. -/
def hwcap_rv64gc : word := Z_to_bv 64 0x112D
def hwcap_rv64gcv : word := Z_to_bv 64 0x20112D

/-- The auxiliary vector the model's kernel provides, terminated by
AT_NULL.  AT_UID = AT_EUID = uid and AT_SECURE = 0 by construction (a
secure-exec is not an input `State.ProcInput` can express). -/
def auxv_entries (ph : PhdrInfo) (at_random : word) (uid hwcap : word) : List (word × word) :=
  [ (AT_PHDR,   Z_to_bv 64 (ph.ph_addr : Int)),
    (AT_PHENT,  Z_to_bv 64 (ph.ph_ent : Int)),
    (AT_PHNUM,  Z_to_bv 64 (ph.ph_num : Int)),
    (AT_HWCAP,  hwcap),
    (AT_PAGESZ, Z_to_bv 64 4096),
    (AT_UID,    uid),
    (AT_EUID,   uid),
    (AT_SECURE, Z_to_bv 64 0),
    (AT_RANDOM, at_random),
    (AT_NULL,   Z_to_bv 64 0) ]

/-- Serialize an auxv: each entry is two little-endian 64-bit words. -/
def build_auxv (entries : List (word × word)) : List byte :=
  entries.flatMap (fun e => word_le8 e.1 ++ word_le8 e.2)

def auxv_bytes (ph : PhdrInfo) (at_random : word) (uid hwcap : word) : List byte :=
  build_auxv (auxv_entries ph at_random uid hwcap)

/-- The serialized size is independent of the capability word. -/
def auxv_size : Nat := 160

theorem length_auxv_bytes (ph : PhdrInfo) (at_random uid hwcap : word) :
    (auxv_bytes ph at_random uid hwcap).length = auxv_size := by
  simp [auxv_bytes, build_auxv, auxv_entries, word_le8, auxv_size, List.flatMap]

/-- What `execve` drew for this process's entry stack: the two byte-level
choices in the entry stack image the model does NOT determine, carried
together in `Run.ExecEntry`'s `en_draw`.

`ed_random` is the 16 bytes AT_RANDOM points at (`get_random_bytes` in
`create_elf_tables`, fs/binfmt_elf.c, Linux v6.18.46, commit 1f99e9ab748f).
`ed_slack` is the bytes of the entry stack's LAST PAGE above the block:
Linux's stack is a VMA and a VMA covers whole pages (`setup_arg_pages`,
fs/exec.c, page-aligns its top), and what lies up there is the tail of the
string area, the exec filename AT_EXECFN points at, and the pointer-sized
run of bytes below the VMA's top that `create_init_stack_vma`
(mm/vma_exec.c, Linux v6.18.46) skipped.  This model publishes no AT_EXECFN and builds no
filename string, so no address there has a fixed counterpart in the kernel's
image; the Rocq definition carries the argument for drawing rather than
zeroing them.  Neither half has a validity clause. -/
structure EntryDraw where
  mkDraw ::
  ed_random : BitVec 128
  ed_slack  : word → byte

/-- The 16 bytes AT_RANDOM points at: this run's entropy draw
(the `ed_random` half of `Run.ExecEntry`'s `en_draw`), serialized
little-endian, so byte `k` is
`bv_extract (8 * k) 8 rnd`.  The kernel draws them afresh at every `execve`
(`get_random_bytes` in `create_elf_tables`, fs/binfmt_elf.c, Linux v6.18.46,
commit 1f99e9ab748f); the Rocq definition carries the argument for
quantifying rather than fixing them.  A `BitVec 128` rather than a 16-element
byte list so the length is fixed by the type and the entry needs no validity
clause. -/
def at_random_bytes (rnd : BitVec 128) : List byte :=
  [ bv_extract 0 8 rnd,    bv_extract 8 8 rnd,
    bv_extract 16 8 rnd,   bv_extract 24 8 rnd,
    bv_extract 32 8 rnd,   bv_extract 40 8 rnd,
    bv_extract 48 8 rnd,   bv_extract 56 8 rnd,
    bv_extract 64 8 rnd,   bv_extract 72 8 rnd,
    bv_extract 80 8 rnd,   bv_extract 88 8 rnd,
    bv_extract 96 8 rnd,   bv_extract 104 8 rnd,
    bv_extract 112 8 rnd,  bv_extract 120 8 rnd ]

theorem length_at_random_bytes (rnd : BitVec 128) : (at_random_bytes rnd).length = 16 := rfl

def at_random_ptr (sp : word) (argv envp : List (List byte)) : word :=
  let struct_size :=
    8 + (argv.length + 1) * 8 + (envp.length + 1) * 8 + auxv_size
  let len := struct_size + (flatten_strings argv).length + (flatten_strings envp).length
  let pad := (8 - len % 8) % 8
  sp + nat_to_word (len + pad)

/-- The block the kernel writes on the new stack.  Only the `ed_random` half
of `draw` is read, by the final `at_random_bytes` block: no address in the
layout moves with the draw (`build_stack_bytes_split_random` in the Rocq
twin).  What the model MAPS is `Run.entry_stack_image`, this block followed
by the rest of the page it ends in. -/
def build_stack_bytes (ph : PhdrInfo) (sp : word) (argv : List (List byte))
    (envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw) : List byte :=
  let argc := len_word argv
  let envc := envp.length
  let n_argv_slots := argv.length + 1
  let n_envp_slots := envc + 1
  let auxv := auxv_bytes ph (at_random_ptr sp argv envp) uid hwcap
  let struct_size := 8 + n_argv_slots * 8 + n_envp_slots * 8 + auxv.length
  let string_base := sp + nat_to_word struct_size
  let (argv_ptrs, env_str_base) := string_addrs string_base argv
  let (envp_ptrs, _) := string_addrs env_str_base envp
  let raw :=
    word_le8 argc
    ++ argv_ptrs.flatMap word_le8
    ++ word_le8 (Z_to_bv 64 0)
    ++ envp_ptrs.flatMap word_le8
    ++ word_le8 (Z_to_bv 64 0)
    ++ auxv
    ++ flatten_strings argv
    ++ flatten_strings envp
  let len := raw.length
  let pad := (8 - len % 8) % 8
  raw ++ List.replicate pad (Z_to_bv 8 0) ++ at_random_bytes draw.ed_random

/-- The stack image as a partial byte map based at `base`. -/
def stack_to_mem (base : word) (bytes : List byte) : word → Option byte :=
  fun addr =>
    if bv_unsigned base ≤ bv_unsigned addr then
      let off := bv_unsigned addr - bv_unsigned base
      if off < (bytes.length : Int) then
        bytes[Int.toNat off]?
      else none
    else none

end LinuxProcessSemantics.LinuxProcessSem.StackLayout
