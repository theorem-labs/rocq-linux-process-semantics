import LinuxProcessSemantics.LinuxProcessSem.BvBase
import LinuxProcessSemantics.LinuxProcessSem.MemImageType
import LinuxProcessSemantics.Riscv.Decode
import LinuxProcessSemantics.Riscv.DecodeC
import LinuxProcessSemantics.Riscv.Sem

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.RiscvSemantics — user-mode RISC-V step over Linux virtual memory

Mirrors `theories/LinuxProcessSem/RiscvSemantics.v`, definition for
definition; the Rocq header carries the design.  In one paragraph: (a) ISA
WRAPPING — fetch from the static segment image (length-correct,
compressed-aware), intercept ECALL before decode, decode with
`DecodeC.decode_any`, build the effect tree with `Sem.exec` and interpret
it; (b) VIRTUAL MEMORY — the loaded segments as a read-only backing gated on
'r', a writable overlay for stores gated on the writable view (`store_ok`,
the SIGSEGV analogue), fetch gated on 'x' (NX), and the read vs. writable
views the syscall specs use.

TRUST BOUNDARY: this file is part of the trusted specification.

The two failure kinds are kept APART and it matters (see `machine_result`):
`MachineFault` is the PROGRAM dying faithfully; `MachineUnmodeled` is the
MODEL giving up, fail closed.  The Lean port has more of the latter than
Rocq does (compressed instructions, F/D — see `lean/README.md`), never
more of the former. -/

namespace LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType

/-! ## Machine state -/

structure machine_state where
  ms_regs        : bvmap 5 word
  ms_fregs       : bvmap 5 word
  ms_pc_val      : word
  ms_svc_pending : Option word
  ms_resv        : Option word
  ms_fcsr        : BitVec 32
  ms_mem         : word → Option byte
  ms_rom         : word → Option byte

def ms_pc (st : machine_state) : word := st.ms_pc_val

def ms_sp (st : machine_state) : word := reg_get st.ms_regs 2

/-- `ms_gpr st i` returns the i-th syscall argument register (a0–a5):
arg i → x(10+i). -/
def ms_gpr (st : machine_state) (i : Nat) : word :=
  reg_get st.ms_regs (Z_to_bv 5 (10 + (i : Int)))

/-- Read physical register by number (x0 reads as 0). -/
def ms_reg (st : machine_state) (r : reg) : word :=
  if bv_eqb r 0 then Z_to_bv 64 0 else reg_get st.ms_regs r

/-- Update a physical register. x0 writes are silently discarded. -/
def set_reg (st : machine_state) (r : reg) (v : word) : machine_state :=
  if bv_eqb r 0 then st
  else { st with ms_regs := bvmap_set r v st.ms_regs }

/-- Set a0 (= x10), the syscall return register. -/
def set_gpr0 (ms : machine_state) (ret : word) : machine_state :=
  set_reg ms 10 ret

/-- Write `data` byte-by-byte into `mem` starting at `addr`. -/
def write_to_mem (mem : word → Option byte) (addr : word)
    (data : List byte) : word → Option byte :=
  match data with
  | [] => mem
  | b :: rest =>
    write_to_mem (fun a => if bv_eqb a addr then some b else mem a)
                 (addr + 1) rest

/-- Set a0 to `ret` and write `data` into memory at `buf_addr`. -/
def set_gpr0_write_buf (ms : machine_state) (ret : word)
    (buf_addr : word) (data : List byte) : machine_state :=
  let ms' := set_reg ms 10 ret
  { ms' with ms_mem := write_to_mem ms'.ms_mem buf_addr data }

/-! ## Machine step result

`MachineFault` — the PROGRAM did something fatal and the model says so
FAITHFULLY (a misaligned pc, a jump to unmapped or non-executable memory,
a load from an unmapped address, a store outside the writable view, an
`ebreak`, a defined-illegal encoding — Linux turns the hart's
illegal-instruction exception into SIGILL with `ILL_ILLOPC` in
`do_trap_insn_illegal`, arch/riscv/kernel/traps.c, Linux v6.18.46,
commit 1f99e9ab748f).  `MachineUnmodeled` — the MODEL gave
up (an undecodable word the ISA does not pin as illegal, an `EIllegal`
boundary node, a fetch declined for a modeling reason).  Both drive the
same explicit error transition in `Run.sstep`; the distinction is carried
alongside it. -/
inductive machine_result (A : Type) : Type
  | MachineOk (result : A)
  | MachineFault
  | MachineUnmodeled

export machine_result (MachineOk MachineFault MachineUnmodeled)

/-! ## Unified memory read helpers -/

def ms_read_byte (ms : machine_state) (addr : word) : Option byte :=
  match ms.ms_mem addr with
  | some b => some b
  | none   => ms.ms_rom addr

def ms_read_bytes_aux (ms : machine_state) (addr : word) (n : Nat)
    : Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    match ms_read_byte ms addr with
    | some b =>
      match ms_read_bytes_aux ms (addr + 1) n' with
      | some rest => some (b :: rest)
      | none => none
    | none => none

def ms_read_bytes (ms : machine_state) (addr len : word)
    : Option (List byte) :=
  ms_read_bytes_aux ms addr (word_to_nat len)

def ms_read_u64 (ms : machine_state) (addr : word) : Option word :=
  match ms_read_bytes ms addr (Z_to_bv 64 8) with
  | some bs => some (le_bytes_to_word bs)
  | none => none

def word_to_le_bytes (n : Nat) (v : word) : List byte :=
  Z_to_le_bytes n (bv_unsigned v)

/-! ## Hex decode helpers

Segment bytes are stored as a hex string (lowercase, no spaces).  Rocq
indexes a `PrimString` BYTE-wise by `Uint63`; a Lean `String` is indexed
here through its UTF-8 bytes (`String.toUTF8`), never its characters, so
the two agree on every string and not only on ASCII ones — on a chunk
holding a multi-byte character the character view would answer a byte
the Rocq reader does not.  A byte at index `i` exists exactly when both
of its nybbles do, `2*i + 1 < size`.  Rocq writes that bound as
`ci1 < len || ci1 = len - 1`; the second disjunct is reached only through
the `len = 0` underflow of `Uint63.sub`, where the out-of-range
`PrimString.get` answers 0 and `hex_nybble` 16, so it adds no byte. -/

def hex_nybble (c : UInt8) : Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then c.toNat - 48
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then c.toNat - 87
  else 16

def hex_byte_at (s : String) (i : Nat) : Option byte :=
  let bs := s.toUTF8
  if hlt : 2 * i + 1 < bs.size then
    let h := hex_nybble (bs[2 * i]'(by omega))
    let l := hex_nybble (bs[2 * i + 1]'hlt)
    if h < 16 ∧ l < 16
    then some (Z_to_bv 8 ((h * 16 + l : Nat) : Int))
    else none
  else none

def hex_read_bytes (s : String) (off : Nat) (n : Nat) : Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    match hex_byte_at s off with
    | none => none
    | some b =>
      match hex_read_bytes s (off + 1) n' with
      | none => none
      | some rest => some (b :: rest)

/-- Read through the bounded strings that represent one logical ELF
segment.  Chunk boundaries have no memory-semantic meaning. -/
def segment_byte_at (chunks : List String) (off : Nat) : Option byte :=
  match chunks with
  | [] => none
  | chunk :: rest =>
      let chunk_bytes := chunk.utf8ByteSize / 2
      if off < chunk_bytes
      then hex_byte_at chunk off
      else segment_byte_at rest (off - chunk_bytes)

def segment_read_bytes (bytes : List String) (off : Nat) (n : Nat)
    : Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
      match segment_byte_at bytes off with
      | none => none
      | some b =>
          match segment_read_bytes bytes (off + 1) n' with
          | none => none
          | some rest => some (b :: rest)

/-! ## Memory read -/

/-- Linear scan over the loaded segments for one whose range covers
`[addr .. addr + n - 1]`, in `Int` over unsigned values. -/
def find_segment (segs : List Segment) (addr : Int) (n : Int) : Option Segment :=
  match segs with
  | [] => none
  | seg :: rest =>
    let base : Int := seg.seg_base
    let top  : Int := base + seg.seg_size
    if base ≤ addr && addr + n ≤ top
    then some seg
    else find_segment rest addr n

/-- Read `n` bytes at `addr` from segment `seg`, overlay first, static
image otherwise. -/
def seg_ov_read_bytes (m : word → Option byte) (seg : Segment)
    (addr : word) (n : Nat) : Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    match (match m addr with
           | some b => some b
           | none => segment_byte_at seg.seg_bytes
                       (Int.toNat (bv_unsigned addr - seg.seg_base))) with
    | some b =>
      match seg_ov_read_bytes m seg (addr + 1) n' with
      | some rest => some (b :: rest)
      | none => none
    | none => none

/-- Does `[addr .. addr + n)` avoid every NON-writable loaded segment? -/
def range_avoids_ro_segs (segs : List Segment) (addr n : Int) : Bool :=
  segs.all (fun seg =>
             seg_writable seg
             || !((seg.seg_base : Int) < addr + n
                  && addr < (seg.seg_base : Int) + seg.seg_size))

section WithMemImage

variable (mi_loaded_segments : List Segment)

/-- DATA read: `[addr .. addr+n)` only if it lies in a single READABLE
segment. -/
def memory_read (addr : word) (n : Nat) : Option (List byte) :=
  match find_segment mi_loaded_segments (bv_unsigned addr) n with
  | some seg =>
    if seg_readable seg then
      let off := Int.toNat (bv_unsigned addr - seg.seg_base)
      segment_read_bytes seg.seg_bytes off n
    else none
  | none => none

/-- INSTRUCTION read from an IMMUTABLE executable segment (x and not w):
the static image is the truth there. -/
def code_read (addr : word) (n : Nat) : Option (List byte) :=
  match find_segment mi_loaded_segments (bv_unsigned addr) n with
  | some seg =>
    if seg_executable seg && !(seg_writable seg) then
      let off := Int.toNat (bv_unsigned addr - seg.seg_base)
      segment_read_bytes seg.seg_bytes off n
    else none
  | none => none

/-- The STATIC projection of the w+x fetch. -/
def code_read_wx (addr : word) (n : Nat) : Option (List byte) :=
  match find_segment mi_loaded_segments (bv_unsigned addr) n with
  | some seg =>
    if seg_executable seg && seg_writable seg then
      let off := Int.toNat (bv_unsigned addr - seg.seg_base)
      segment_read_bytes seg.seg_bytes off n
    else none
  | none => none

/-- INSTRUCTION read from a WRITABLE executable (w+x) segment, through the
overlay-first view. -/
def code_read_ov (m : word → Option byte) (addr : word) (n : Nat)
    : Option (List byte) :=
  match find_segment mi_loaded_segments (bv_unsigned addr) n with
  | some seg =>
    if seg_executable seg && seg_writable seg then
      seg_ov_read_bytes m seg addr n
    else none
  | none => none

/-- `fetch_byte_traps a` is true exactly when a real MMU would trap on
fetching the single byte `a`: unmapped, or its page lacks 'x'. -/
def fetch_byte_traps (a : word) : Bool :=
  match find_segment mi_loaded_segments (bv_unsigned a) 1 with
  | none => true
  | some seg => !(seg_executable seg)

/-! ## Writable memory view -/

/-- The byte at `addr` as the KERNEL may write it: the writable overlay
merged over segments carrying 'w'. -/
def wview (m : word → Option byte) (addr : word) : Option byte :=
  match m addr with
  | some b => some b
  | none =>
      match find_segment mi_loaded_segments (bv_unsigned addr) 1 with
      | some seg =>
          if seg_writable seg
          then segment_byte_at seg.seg_bytes
                 (Int.toNat (bv_unsigned addr - seg.seg_base))
          else none
      | none => none

def ms_writable_byte (ms : machine_state) (addr : word) : Option byte :=
  wview mi_loaded_segments ms.ms_mem addr

/-- The store bound: every byte of `[a .. a+n)` must be in the writable
view.  See the Rocq note for why loads need no such bound. -/
def store_ok (m : word → Option byte) (a : word) (n : Nat) : Bool :=
  match n with
  | 0 => true
  | n' + 1 =>
      match wview mi_loaded_segments m a with
      | some _ => store_ok m (a + 1) n'
      | none => false

/-! ## Instruction fetch -/

/-- Four bytes from an IMMUTABLE executable segment, little-endian; `none`
on a misaligned `addr` (IALIGN=16 with C). -/
def fetch_word (addr : word) : Option (BitVec 32) :=
  if !(bv_unsigned addr % 2 = 0) then none
  else
  match code_read mi_loaded_segments addr 4 with
  | some [b0, b1, b2, b3] => some (le4 b3 b2 b1 b0)
  | _ => none

def fetch_word_ov (m : word → Option byte) (addr : word) : Option (BitVec 32) :=
  if !(bv_unsigned addr % 2 = 0) then none
  else
  match code_read_ov mi_loaded_segments m addr 4 with
  | some [b0, b1, b2, b3] => some (le4 b3 b2 b1 b0)
  | _ => none

def fetch_word_wx (addr : word) : Option (BitVec 32) :=
  if !(bv_unsigned addr % 2 = 0) then none
  else
  match code_read_wx mi_loaded_segments addr 4 with
  | some [b0, b1, b2, b3] => some (le4 b3 b2 b1 b0)
  | _ => none

/-! ## Halfword-granular instruction fetch (RVC-correct) -/

def fetch_half (addr : word) : Option (BitVec 16) :=
  match code_read mi_loaded_segments addr 2 with
  | some [b0, b1] => some (le2 b1 b0)
  | _ => none

def fetch_tail (addr : word) : Option (BitVec 32) :=
  if !(bv_unsigned addr % 2 = 0) then none
  else
  match fetch_half mi_loaded_segments addr with
  | none => none
  | some h0 =>
    if (bits 0 2 h0).toNat = 3 then
      match fetch_half mi_loaded_segments (addr + 2) with
      | some h1 => some (h1 ++ h0)
      | none => none
    else
      some ((0 : BitVec 16) ++ h0)

def fetch_half_ov (m : word → Option byte) (addr : word) : Option (BitVec 16) :=
  match code_read_ov mi_loaded_segments m addr 2 with
  | some [b0, b1] => some (le2 b1 b0)
  | _ => none

def fetch_half_any (m : word → Option byte) (addr : word) : Option (BitVec 16) :=
  match fetch_half mi_loaded_segments addr with
  | some h => some h
  | none => fetch_half_ov mi_loaded_segments m addr

def fetch_tail_any (m : word → Option byte) (addr : word) : Option (BitVec 32) :=
  if !(bv_unsigned addr % 2 = 0) then none
  else
  match fetch_half_any mi_loaded_segments m addr with
  | none => none
  | some h0 =>
    if (bits 0 2 h0).toNat = 3 then
      match fetch_half_any mi_loaded_segments m (addr + 2) with
      | some h1 => some (h1 ++ h0)
      | none => none
    else
      some ((0 : BitVec 16) ++ h0)

/-- RISC-V ECALL encoding is exactly 0x00000073. -/
def is_ecall (w : BitVec 32) : Bool :=
  bv_eqb w (Z_to_bv 32 0x73)

/-! ## ISA-semantics integration -/

/-- Byte counts for the `ELoad`/`EStore` widths (in BITS). -/
def width_bytes (n : Nat) : Nat :=
  match n with
  | 8 => 1 | 16 => 2 | 32 => 4 | 64 => 8
  | _ => 0

def width_bytesZ (n : Nat) : Int :=
  match n with
  | 8 => 1 | 16 => 2 | 32 => 4 | 64 => 8
  | _ => 0

/-- Overlay-then-segments memory read: fail on any miss. -/
def ov_read_bytes (m : word → Option byte) (addr : word) (n : Nat)
    : Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    match (match m addr with
           | some b => some b
           | none => match memory_read mi_loaded_segments addr 1 with
                     | some (b :: _) => some b
                     | _ => none) with
    | some b =>
      match ov_read_bytes m (addr + 1) n' with
      | some rest => some (b :: rest)
      | none => none
    | none => none

/-! ### Memory accesses reported by the tree interpreter -/

def memory_access : Type := word × Nat

structure access_report (A : Type) where
  mkAccessReport ::
  access_value : A
  accessed_ranges : List memory_access

def drop_access_report {A : Type} (r : machine_result (access_report A))
    : machine_result A :=
  match r with
  | MachineOk report => MachineOk report.access_value
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled

/-- The tree interpreter.  `EEbreak`, `EFault` and `EDefinedIllegal` are
`MachineFault` (the process dies); `EIllegal` and `EEcall` are
`MachineUnmodeled` (the model declined; `EEcall` is unreachable since ECALL
is intercepted before decode); a failed load or store is `MachineFault`
(the SIGSEGV analogue). -/
def interp_eff_accesses (t : eff) (m : word → Option byte)
    : machine_result (access_report (core × (word → Option byte))) :=
  match t with
  | .EDone c => MachineOk (access_report.mkAccessReport (c, m) [])
  | .EEbreak _ | .EFault _ | .EDefinedIllegal _ => MachineFault
  | .EIllegal _ | .EEcall _ => MachineUnmodeled
  | .ELoad n a k =>
      match ov_read_bytes mi_loaded_segments m a (width_bytes n) with
      | some bs =>
        match interp_eff_accesses
                (k (bv_extract 0 n (le_bytes_to_word bs))) m with
        | MachineOk report =>
          MachineOk
            (access_report.mkAccessReport report.access_value
               ((a, width_bytes n) :: report.accessed_ranges))
        | MachineFault => MachineFault
        | MachineUnmodeled => MachineUnmodeled
      | none => MachineFault
  | .EStore n a v k =>
      if store_ok mi_loaded_segments m a (width_bytes n)
      then
        match interp_eff_accesses k
                (write_to_mem m a
                   (Z_to_le_bytes (width_bytes n) (bv_unsigned v))) with
        | MachineOk report =>
          MachineOk
            (access_report.mkAccessReport report.access_value
               ((a, width_bytes n) :: report.accessed_ranges))
        | MachineFault => MachineFault
        | MachineUnmodeled => MachineUnmodeled
      else MachineFault

/-- There is one trusted interpreter.  Callers that do not need access
observations project them away from its result. -/
def interp_eff (t : eff) (m : word → Option byte)
    : machine_result (core × (word → Option byte)) :=
  drop_access_report (interp_eff_accesses mi_loaded_segments t m)

theorem drop_interp_eff_accesses (t : eff) (m : word → Option byte) :
    drop_access_report (interp_eff_accesses mi_loaded_segments t m)
      = interp_eff mi_loaded_segments t m := rfl

/-! ## Decode-and-execute a fetched instruction word -/

def decode_exec_accesses (st : machine_state) (w : BitVec 32)
    : machine_result (access_report machine_state) :=
  if is_ecall w then
    MachineOk (access_report.mkAccessReport
      { st with ms_svc_pending := some (ms_reg st 17) } [])
  else
    match decode_any w with
    | none =>
      if is_defined_illegal w then MachineFault else MachineUnmodeled
    | some (i, isz) =>
      match interp_eff_accesses mi_loaded_segments
              (exec (Z_to_bv 64 isz) i
                 (core.Core st.ms_regs st.ms_fregs st.ms_pc_val st.ms_fcsr st.ms_resv))
              st.ms_mem with
      | MachineFault => MachineFault
      | MachineUnmodeled => MachineUnmodeled
      | MachineOk report =>
        let (c, m') := report.access_value
        MachineOk (access_report.mkAccessReport
          { ms_regs := c.c_regs, ms_fregs := c.c_fregs,
            ms_pc_val := c.c_pc,
            ms_svc_pending := none,
            ms_resv := c.c_resv, ms_fcsr := c.c_fcsr,
            ms_mem := m',
            ms_rom := st.ms_rom }
          report.accessed_ranges)

def decode_exec (st : machine_state) (w : BitVec 32) : machine_result machine_state :=
  drop_access_report (decode_exec_accesses mi_loaded_segments st w)

/-! ## Step function -/

/-- Classify a fetch at `addr` that every fetch path declined. -/
def fetch_failure (m : word → Option byte) (addr : word)
    : machine_result machine_state :=
  if !(bv_unsigned addr % 2 = 0) then MachineFault
  else
    let traps :=
      (fetch_byte_traps mi_loaded_segments addr
       || fetch_byte_traps mi_loaded_segments (addr + 1)
       || match fetch_half_any mi_loaded_segments m addr with
          | none => false
          | some _ =>
            (fetch_byte_traps mi_loaded_segments (addr + 2)
             || fetch_byte_traps mi_loaded_segments (addr + 3)))
    if traps then MachineFault else MachineUnmodeled

def step_accesses (st : machine_state) : machine_result (access_report machine_state) :=
  match fetch_word mi_loaded_segments (ms_pc st) with
  | some w => decode_exec_accesses mi_loaded_segments st w
  | none =>
    match fetch_word_ov mi_loaded_segments st.ms_mem (ms_pc st) with
    | some w => decode_exec_accesses mi_loaded_segments st w
    | none =>
      match fetch_tail_any mi_loaded_segments st.ms_mem (ms_pc st) with
      | some w => decode_exec_accesses mi_loaded_segments st w
      | none =>
        match fetch_failure mi_loaded_segments st.ms_mem (ms_pc st) with
        | MachineOk st' => MachineOk (access_report.mkAccessReport st' [])
        | MachineFault => MachineFault
        | MachineUnmodeled => MachineUnmodeled

def step (st : machine_state) : machine_result machine_state :=
  drop_access_report (step_accesses mi_loaded_segments st)

theorem drop_decode_exec_accesses (st : machine_state) (w : BitVec 32) :
    drop_access_report (decode_exec_accesses mi_loaded_segments st w)
      = decode_exec mi_loaded_segments st w := rfl

theorem drop_step_accesses (st : machine_state) :
    drop_access_report (step_accesses mi_loaded_segments st)
      = step mi_loaded_segments st := rfl

end WithMemImage

end LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
