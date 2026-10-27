(** * LinuxProcessSem.RiscvSemantics — user-mode RISC-V step over Linux virtual memory

    TRUST BOUNDARY: this file is part of the trusted specification.

    Uses the RV64GC ISA semantics in [theories/Riscv]
    (LinuxProcessSemantics.Riscv): registers and addresses are
    [word = bv 64], memory bytes are [byte = bv 8], register indices
    are [reg = bv 5].

    This file does two things:

    (a) ISA WRAPPING.  It wraps the ISA decoder/executor into a
        total-or-illegal step function over this project's
        [machine_state]: fetch the instruction from the STATIC segment
        image, check for ECALL (intercepted before decode so the syscall
        model can take over), otherwise decode with [DecodeC.decode_any]
        (32-bit or compressed), build the instruction's EFFECT TREE
        with [Sem.exec] and interpret it ([interp_eff]); a failing
        interpretation is the illegal transition.

        - COMPRESSED instructions (RV64GC) are decoded and executed, and
          instruction fetch is LENGTH-CORRECT: [fetch_tail] reads the
          first 16-bit parcel and only reads the second when that parcel
          marks a 32-bit instruction, so a 2-byte instruction in the
          last 2 mapped bytes of a segment (or just before a
          non-executable page) fetches from exactly those two bytes
          instead of spuriously faulting.  A four-byte [fetch_word] fast
          path handles the common case; it is sound under the segments'
          non-overlap invariant (see the [fetch_tail] note).
        - LR/SC reservations are MODELED ([ms_resv]).
        - F/D and the fcsr Zicsr accesses are MODELED: the machine
          state carries the FP register file ([ms_fregs]) and fcsr
          ([ms_fcsr]) and threads both through [Sem.core], so IEEE
          arithmetic and its accrued exception flags are ordinary
          state transitions here rather than a modeling boundary.

    (b) VIRTUAL MEMORY.  What the program can read, write and execute is
        not a hardware fact — it is the address space Linux sets up for a
        user process, honouring the per-segment ELF page permissions
        (r/w/x):
        - the loaded segments as a read-only backing ([ms_rom]), gated
          on 'r' so a load from a PROT_NONE page faults ([memory_read]);
        - a writable overlay for everything the process stores
          ([ms_mem]), with stores outside the WRITABLE view made
          illegal (the SIGSEGV analogue, [store_ok]) — a store must
          land on memory the process actually has mapped, not merely
          miss the read-only segments;
        - instruction fetch gated on 'x', so jumping into a
          non-executable segment faults instead of running its bytes as
          code (the NX guarantee).  Fetch reads the view a real machine
          executes: for an IMMUTABLE executable segment (x and not w —
          stores into it are illegal, [store_ok]) it reads the static
          segment image directly ([code_read]/[fetch_word]); for a
          WRITABLE executable segment (w+x, as GNU ld's default
          [-z noseparate-code] produces by merging .text with the
          writable sections) it reads the writable overlay first and
          falls back to the static image
          ([code_read_ov]/[fetch_word_ov]), exactly as data loads do —
          so a store into a w+x segment is observed by the next fetch
          at that address, and an ordinary w+x binary (one that never
          stores over its own code) executes its image bytes faithfully;
        - the READ vs. WRITABLE views ([ms_read_byte] vs.
          [ms_writable_byte]) that the syscall specs use for buffer
          checks (the copy_to_user/EFAULT split).
        Segment data stays in the [N]-based [MemImageType.Segment];
        all range
        arithmetic against segments happens in [Z] over [bv_unsigned].

    ECALL detection:
    RISC-V ECALL encoding = 0x00000073.  When detected, we record the
    syscall number from register a7 (x17) in [ms_svc_pending]; the
    trace semantics (Run.v) dispatches it on the next step.  Linux
    riscv64 ABI: syscall number in a7, args in a0–a5 (x10–x15). *)

From Stdlib Require Import ZArith NArith List String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
Open Scope bv_scope.
Local Open Scope bool_scope.

(** ** Machine state

    [machine_state] holds the general-purpose registers (as a
    [bvmap 5 word], the SAME representation [Sem.core] uses, so [step]
    threads the register file through the ISA layer with no conversion;
    missing keys read as 0 and register x0 is forced to 0 by the
    read/write wrappers per the RISC-V spec), the program counter, a
    pending-ecall slot, the LR/SC reservation, writable memory, and
    read-only memory.

    Register convention (Linux riscv64 syscall ABI):
    - x17 (a7): syscall number
    - x10–x15 (a0–a5): syscall arguments
    - x10 (a0): return value *)

Record machine_state := {
  ms_regs        : bvmap 5 word;
  ms_fregs       : bvmap 5 word;
  ms_pc_val      : word;
  ms_svc_pending : option word;
  ms_resv        : option word;
  ms_fcsr        : bv 32;
  ms_mem         : word -> option byte;
  ms_rom         : word -> option byte
}.

Definition ms_pc (st : machine_state) : word := st.(ms_pc_val).

Definition ms_sp (st : machine_state) : word := reg_get st.(ms_regs) 2.

(** [ms_gpr st i] returns the i-th syscall argument register (a0–a5).
    Maps argument index to physical register: arg i → x(10+i). *)
Definition ms_gpr (st : machine_state) (i : nat) : word :=
  reg_get st.(ms_regs) (Z_to_bv 5 (10 + Z.of_nat i)).

(** Read physical register by number (x0 reads as 0). *)
Definition ms_reg (st : machine_state) (r : reg) : word :=
  if bv_eqb r 0 then Z_to_bv 64 0 else reg_get st.(ms_regs) r.

(** Update a physical register. x0 writes are silently discarded. *)
Definition set_reg (st : machine_state) (r : reg) (v : word) : machine_state :=
  if bv_eqb r 0 then st
  else {| ms_regs := bvmap_set r v st.(ms_regs); ms_fregs := st.(ms_fregs);
          ms_pc_val := st.(ms_pc_val);
          ms_svc_pending := st.(ms_svc_pending);
          ms_resv := st.(ms_resv); ms_fcsr := st.(ms_fcsr);
          ms_mem := st.(ms_mem);
          ms_rom := st.(ms_rom) |}.

(** Set a0 (= x10), the syscall return register. *)
Definition set_gpr0 (ms : machine_state) (ret : word) : machine_state :=
  set_reg ms 10 ret.

(** Write [data] byte-by-byte into [mem] starting at [addr]. *)
Fixpoint write_to_mem (mem : word -> option byte) (addr : word)
    (data : list byte) : word -> option byte :=
  match data with
  | [] => mem
  | b :: rest =>
    write_to_mem (fun a => if bv_eqb a addr then Some b else mem a)
                 (addr + 1) rest
  end.

(** Set a0 to [ret] and write [data] into memory at [buf_addr] — the
    post-state of a syscall that returns a value and fills a caller buffer. *)
Definition set_gpr0_write_buf (ms : machine_state) (ret : word)
    (buf_addr : word) (data : list byte) : machine_state :=
  let ms' := set_reg ms 10 ret in
  {| ms_regs := ms_regs ms'; ms_fregs := ms_fregs ms';
     ms_pc_val := ms_pc_val ms';
     ms_svc_pending := ms_svc_pending ms';
     ms_resv := ms_resv ms'; ms_fcsr := ms_fcsr ms';
     ms_mem := write_to_mem (ms_mem ms') buf_addr data;
     ms_rom := ms_rom ms' |}.

(** ** Machine step result

    A single machine step either succeeds ([MachineOk]) or does not, and
    the two ways of not succeeding are kept APART, because they mean
    opposite things about this development:

    - [MachineFault] — the PROGRAM did something fatal and the model says
      so FAITHFULLY: a misaligned pc, a jump to an address that is
      unmapped or mapped without 'x', a load from an unmapped address, a
      store to an address the process has not mapped writable — into a
      read-only segment, or into nothing at all (the SIGSEGV
      analogue) — or an
      [ebreak] (the SIGTRAP analogue), or an encoding the ISA defines
      to be illegal in every implementation — the SIGILL analogue, which
      arrives on two routes: an undecodable word
      [DecodeC.is_defined_illegal] flags (the all-zero parcel), and a
      decodable instruction [Sem.exec] answers with [Sem.EDefinedIllegal]
      (a write to a read-only CSR; see [Sem.csr_write_illegal]).  Linux
      turns the hart's illegal-instruction exception into SIGILL with
      [ILL_ILLOPC] in [do_trap_insn_illegal]
      (arch/riscv/kernel/traps.c, v6.18.46), so a real
      Linux process dies here too.  A source binary is allowed to fault;
      the model has modeled it.

    - [MachineUnmodeled] — the MODEL gave up: a word this development's
      decoder does not decode (unless the ISA defines it illegal — see
      above), an ISA-level [EIllegal] boundary node, or a fetch
      [code_read] declined for a modeling
      reason rather than a hardware one (a w+x segment, or snapshot hex
      the decoder cannot read — see [fetch_failure]).  Nothing is
      claimed about what the real process would do.  A source binary
      reaching this makes its equivalence statement suspect (see
      [Run.reaches_unmodeled] and the [modeled] clause of
      [Equivalence.strong_equiv]), which is exactly why the
      classification is fail-closed: anything that might be a gap in the
      decoder, in the ISA semantics, or in the memory image counts
      as [MachineUnmodeled], and only failures a real process would also
      suffer count as [MachineFault].

    Both drive the same explicit error transition in [Run.sstep]; the
    distinction is carried alongside it, not instead of it.  The machine
    itself is deterministic — all non-determinism in the semantics lives
    in the syscall model. *)
Inductive machine_result (A : Type) :=
| MachineOk (result : A) : machine_result A
| MachineFault : machine_result A
| MachineUnmodeled : machine_result A.

Arguments MachineOk {A}.
Arguments MachineFault {A}.
Arguments MachineUnmodeled {A}.

(** ** Unified memory read helpers

    [ms_read_byte] checks writable memory first, then falls back to
    read-only memory. *)

Definition ms_read_byte (ms : machine_state) (addr : word) : option byte :=
  match ms_mem ms addr with
  | Some b => Some b
  | None   => ms_rom ms addr
  end.

Fixpoint ms_read_bytes_aux (ms : machine_state) (addr : word) (n : nat)
    : option (list byte) :=
  match n with
  | O => Some []
  | S n' =>
    match ms_read_byte ms addr with
    | Some b =>
      match ms_read_bytes_aux ms (addr + 1) n' with
      | Some rest => Some (b :: rest)
      | None => None
      end
    | None => None
    end
  end.

Definition ms_read_bytes (ms : machine_state) (addr len : word)
    : option (list byte) :=
  ms_read_bytes_aux ms addr (word_to_nat len).

Definition ms_read_u64 (ms : machine_state) (addr : word) : option word :=
  match ms_read_bytes ms addr (Z_to_bv 64 8) with
  | Some bs => Some (le_bytes_to_word bs)
  | None => None
  end.

Definition word_to_le_bytes (n : nat) (v : word) : list byte :=
  Z_to_le_bytes n (bv_unsigned v).

(** ** Hex decode helpers

    Segment bytes are stored as a hex string (lowercase, no spaces).
    These functions decode a contiguous range of bytes from a hex
    string without materialising the whole segment.  Offsets are [N]
    (they index into the [N]-based [Segment] snapshot data). *)

Definition hex_nybble (c : char63) : N :=
  if (Uint63.leb 48 c && Uint63.leb c 57)%bool
  then Z.to_N (Uint63.to_Z c - 48)
  else if (Uint63.leb 97 c && Uint63.leb c 102)%bool
  then Z.to_N (Uint63.to_Z c - 87)
  else 16%N.

Definition hex_byte_at (s : PrimString.string) (i : N) : option byte :=
  let ci  := Uint63.of_Z (Z.of_N (2 * i)) in
  let ci1 := Uint63.of_Z (Z.of_N (2 * i + 1)) in
  let s_len := PrimString.length s in
  if (Uint63.ltb ci1 s_len || Uint63.eqb ci1 (Uint63.sub s_len 1))%bool then
    let hi := PrimString.get s ci in
    let lo := PrimString.get s ci1 in
    let h := hex_nybble hi in
    let l := hex_nybble lo in
    if (N.ltb h 16 && N.ltb l 16)%bool
    then Some (Z_to_bv 8 (Z.of_N (h * 16 + l)))
    else None
  else None.

Fixpoint hex_read_bytes (s : PrimString.string) (off : N) (n : nat)
    : option (list byte) :=
  match n with
  | O => Some []
  | S n' =>
    match hex_byte_at s off with
    | None => None
    | Some b =>
      match hex_read_bytes s (off + 1) n' with
      | None => None
      | Some rest => Some (b :: rest)
      end
    end
  end.

(** Read through the bounded primitive strings that represent one logical ELF
    segment.  Chunk boundaries have no memory-semantic meaning: a load or
    instruction fetch may cross one exactly as it crosses any other byte in
    the segment. *)
Fixpoint segment_byte_at
    (chunks : list PrimString.string) (off : N) : option byte :=
  match chunks with
  | [] => None
  | chunk :: rest =>
      let chunk_bytes :=
        Z.to_N (Uint63.to_Z (PrimString.length chunk) / 2) in
      if (off <? chunk_bytes)%N
      then hex_byte_at chunk off
      else segment_byte_at rest (off - chunk_bytes)
  end.

Fixpoint segment_read_bytes
    (bytes : list PrimString.string) (off : N) (n : nat)
    : option (list byte) :=
  match n with
  | O => Some []
  | S n' =>
      match segment_byte_at bytes off with
      | None => None
      | Some b =>
          match segment_read_bytes bytes (off + 1) n' with
          | None => None
          | Some rest => Some (b :: rest)
          end
      end
  end.

(** ** Memory read

    Linear scan over [loaded_segments] looking for a segment whose
    address range covers [addr .. addr + n - 1].  The range check is in
    [Z] over unsigned values (segments are [N]-based snapshot data and
    never wrap). *)
Fixpoint find_segment (segs : list Segment) (addr : Z) (n : Z)
  : option Segment :=
  match segs with
  | [] => None
  | seg :: rest =>
    let base := Z.of_N seg.(seg_base) in
    let top  := (base + Z.of_N seg.(seg_size))%Z in
    if Z.leb base addr && Z.leb (addr + n) top
    then Some seg
    else find_segment rest addr n
  end.

(** Read [n] bytes at [addr] from segment [seg], each byte taken from
    the writable overlay [m] when present and from the segment's static
    image otherwise — the per-segment analogue of [ov_read_bytes],
    used by [code_read_ov] to fetch from a WRITABLE executable (w+x)
    segment.  Fail on any byte that neither view supplies. *)
Fixpoint seg_ov_read_bytes (m : word -> option byte) (seg : Segment)
    (addr : word) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' =>
    match (match m addr with
           | Some b => Some b
           | None => segment_byte_at seg.(seg_bytes)
                       (Z.to_N (bv_unsigned addr - Z.of_N seg.(seg_base)))
           end) with
    | Some b =>
      match seg_ov_read_bytes m seg (addr + 1) n' with
      | Some rest => Some (b :: rest)
      | None => None
      end
    | None => None
    end
  end.

(** ** Store-target permission check

    Does [addr .. addr + n) avoid every NON-writable loaded segment?
    Machine stores whose target overlaps a segment mapped without 'w'
    (.text, .rodata) are ILLEGAL instructions — the explicit error
    transition, matching the SIGSEGV a real MMU delivers.  (Fetch
    reading the static segment image ([code_read]) is sound for exactly
    these segments: a non-writable executable segment is immutable.
    Fetch from a WRITABLE executable segment reads through the overlay
    instead ([code_read_ov]), so a store into a w+x segment — legal,
    the segment is writable — is observed by later fetches.) *)
Definition range_avoids_ro_segs (segs : list Segment) (addr n : Z) : bool :=
  forallb (fun seg =>
             seg_writable seg
             || negb (Z.ltb (Z.of_N (seg_base seg)) (addr + n)
                      && Z.ltb addr (Z.of_N (seg_base seg) + Z.of_N (seg_size seg))))
          segs.

Section WithMemImage.

Variable mi_loaded_segments : list Segment.

(** DATA read: return [addr .. addr+n) only if it lies in a single
    READABLE segment.  A load whose target segment lacks the 'r' flag
    (a PROT_NONE / write-only page) reads as unmapped — the SIGSEGV
    analogue — exactly as a store outside the writable view is
    illegal (see [store_ok]).  Used for machine loads and,
    via [Run.init_machine_state]'s [ms_rom], for syscall source
    buffers. *)
Definition memory_read (addr : word) (n : N) : option (list byte) :=
  match find_segment mi_loaded_segments (bv_unsigned addr) (Z.of_N n) with
  | Some seg =>
    if seg_readable seg then
      let off := Z.to_N (bv_unsigned addr - Z.of_N seg.(seg_base)) in
      segment_read_bytes seg.(seg_bytes) off (N.to_nat n)
    else None
  | None => None
  end.

(** INSTRUCTION read: like [memory_read] but gated on the EXECUTABLE
    ('x') flag rather than 'r'.  Instruction fetch ([fetch_word]) reads
    through this, so a jump into a non-executable segment (.rodata,
    .data, or an anonymous data mapping) fetches [None] and faults
    ([MachineFault]) instead of executing the bytes as code — the
    NX / W^X guarantee a real kernel installs.  Kept separate from
    [memory_read] because reading data from an executable page and
    executing bytes from a readable-only page are governed by different
    ELF flags.

    This function covers only IMMUTABLE executable segments (x and not
    w): it reads the STATIC segment image, not the writable overlay
    ([ms_mem]), which is sound exactly because stores into non-writable
    segments are illegal ([store_ok]).  A WRITABLE executable segment
    (w+x) is handled by [code_read_ov] below, which reads through the
    overlay the way data loads do; [step] dispatches between the two.
    The two gates are complementary ([x /\ ~w] here, [x /\ w] there),
    so on any given segment exactly one of them can succeed. *)
Definition code_read (addr : word) (n : N) : option (list byte) :=
  match find_segment mi_loaded_segments (bv_unsigned addr) (Z.of_N n) with
  | Some seg =>
    if seg_executable seg && negb (seg_writable seg) then
      let off := Z.to_N (bv_unsigned addr - Z.of_N seg.(seg_base)) in
      segment_read_bytes seg.(seg_bytes) off (N.to_nat n)
    else None
  | None => None
  end.

(** INSTRUCTION read from a WRITABLE executable (w+x) segment: the
    complementary gate to [code_read] ([x /\ w] rather than [x /\ ~w]).
    A w+x segment's bytes are mutable — stores into it are legal — so
    fetch must read the same view data loads do: the writable overlay
    [m] first, falling back to the static segment image
    ([seg_ov_read_bytes]).  A store over an instruction in a w+x
    segment is therefore observed by the next fetch of that address,
    exactly as on real hardware (self-modifying code is MODELED, not
    refused — though the proof layer only follows programs whose code
    range the overlay never touches; see the frame lemmas in
    Common/WxExec.v).

    [code_read_wx] is the STATIC projection of the same read — the
    segment image alone, same [x /\ w] gate, no overlay parameter.  It
    is what the generated per-example fetch lemmas are stated over for
    a w+x image (a pure function of the snapshot, so [vm_compute] can
    check it); [code_read_ov] coincides with it whenever the overlay
    misses the fetched range. *)
Definition code_read_wx (addr : word) (n : N) : option (list byte) :=
  match find_segment mi_loaded_segments (bv_unsigned addr) (Z.of_N n) with
  | Some seg =>
    if seg_executable seg && seg_writable seg then
      let off := Z.to_N (bv_unsigned addr - Z.of_N seg.(seg_base)) in
      segment_read_bytes seg.(seg_bytes) off (N.to_nat n)
    else None
  | None => None
  end.

Definition code_read_ov (m : word -> option byte) (addr : word) (n : N)
    : option (list byte) :=
  match find_segment mi_loaded_segments (bv_unsigned addr) (Z.of_N n) with
  | Some seg =>
    if seg_executable seg && seg_writable seg then
      seg_ov_read_bytes m seg addr (N.to_nat n)
    else None
  | None => None
  end.

(** ** Why a fetch failed: the MODEL declining vs. the PROCESS crashing

    The combined fetch ([code_read] for immutable code, [code_read_ov]
    for w+x code) declines for several different reasons, and they do
    not mean the same thing about this development:

    1. the byte lies outside every loaded segment — a wild jump into
       unmapped memory, which a real process suffers as SIGSEGV;
    2. the byte lies in a segment mapped without 'x' (.rodata, .data) —
       the NX fault a real kernel delivers;
    3. the byte lies in a fetchable segment but neither the overlay nor
       the [seg_bytes] hex supplies it (a malformed or truncated
       snapshot, e.g. uppercase hex, which [hex_nybble] rejects) — a
       limitation of the snapshot, not of the process.

    Cases 1 and 2 are [MachineFault]; case 3 is the MODEL giving up and
    must be [MachineUnmodeled].  Getting this wrong is not
    cosmetic: calling case 3 a crash would let a source binary that
    runs perfectly on real hardware prove [Run.all_traces_error], take
    [Equivalence.equiv]'s escape and free the target unanalyzed, while
    [Equivalence.modeled] — which deliberately tolerates faults —
    certified the run as covered.  That is exactly the vacuity the
    [modeled] clause exists to rule out.  (A w+x segment is not a
    reason: it is fetched through the overlay and simply executes.)

    So the classification is stated on the FAULT side, per byte, and
    everything else is the model's own limit — which keeps it fail-closed
    under a decline this note has not enumerated (a fetch whose bytes
    straddle two abutting executable segments, say: [find_segment] wants
    ONE segment to cover the whole read, and real hardware does not).
    [fetch_byte_traps a] is true exactly when a real MMU would trap on
    fetching the single byte [a]: it is unmapped (case 1) or its page
    lacks 'x' (case 2).

    [fetch_failure] applies it per NEEDED BYTE rather than per pc: a
    32-bit instruction whose first parcel is fetchable and whose second
    parcel is genuinely unmapped is a fault (pinned by
    [Checks/RiscvCompressedFetch.trunc32_step_illegal]) even though the
    pc itself sits in a perfectly good segment. *)
Definition fetch_byte_traps (a : word) : bool :=
  match find_segment mi_loaded_segments (bv_unsigned a) 1 with
  | None => true                        (* case 1: unmapped — a real fault *)
  | Some seg => negb (seg_executable seg)   (* case 2: no 'x' — a real NX fault *)
  end.

(** ** Writable memory view

    The byte at [addr] as the KERNEL may write it: defined on exactly
    the addresses the process has writable-mapped — the writable
    overlay merged over segments carrying the 'w' permission
    (.data/.bss).  Addresses only in non-writable segments
    (.text/.rodata) and unmapped addresses read [None].  Threaded into
    each syscall as [SyscallInput.in_wmem] (the copy_to_user EFAULT
    analogue); compare [ms_read_byte], the READ view used for source
    buffers. *)
Definition wview (m : word -> option byte) (addr : word) : option byte :=
  match m addr with
  | Some b => Some b
  | None =>
      match find_segment mi_loaded_segments (bv_unsigned addr) 1 with
      | Some seg =>
          if seg_writable seg
          then segment_byte_at seg.(seg_bytes)
                           (Z.to_N (bv_unsigned addr - Z.of_N seg.(seg_base)))
          else None
      | None => None
      end
  end.

Definition ms_writable_byte (ms : machine_state) (addr : word) : option byte :=
  wview (ms_mem ms) addr.

(** ** The store bound

    A byte the PROCESS may store to, and the SAME view the kernel
    writes through ([ms_writable_byte] above, threaded into each
    syscall as the copy_to_user/EFAULT gate).  A store outside it is
    the SIGSEGV a real MMU delivers.

    This has to be checked, and checking only the read-only segments is
    not enough, because the overlay [m] is a TOTAL function: writing
    through it CREATES a mapping wherever it lands.  Without a bound, a
    store to any address off a read-only segment succeeds — below the
    stack, in the gap above the image, anywhere — and the process can
    then read the value back.  Real Linux faults there.

    The consequence is not just infidelity in the small.  [init_sp] and
    the initial break are quantified INDEPENDENTLY for the two binaries
    (ASLR; [Run.valid_sp], [Run.valid_brk], and see the note at
    [Equivalence.strong_universal_T]).  Unbounded stack or heap growth
    therefore collides with something at an address that depends on
    those choices, so a program whose recursion or allocation is driven
    by its input diverges from itself between two admissible
    quantifications — and [strong_universal] is then arguably false
    even for a reference against itself.  Real Linux faults at an
    ASLR-INDEPENDENT point instead: the RLIMIT_STACK window, which
    [Run.init_machine_state] already zero-maps as
    [init_sp - stack_max_size, init_sp).

    So the ledger this needs already exists, and is exactly [wview]:
    the initial stack block and its zero window, every brk/mmap grant
    ([Run.apply_zeros]) minus everything [munmap] took back
    ([Run.apply_unmaps]), and the writable segments (.data/.bss).
    Nothing new is tracked; the store is simply held to the same notion
    of writable memory the syscalls already use.

    LOADS need no such bound — [ov_read_bytes] already fails on any
    byte that is neither in the overlay nor in a readable segment.
    Without [store_ok] the two would be asymmetric. *)
Fixpoint store_ok (m : word -> option byte) (a : word) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match wview m a with
      | Some _ => store_ok m (a + 1) n'
      | None => false
      end
  end.

(** ** Instruction fetch

    Read 4 bytes from [addr] out of an IMMUTABLE executable segment
    ([code_read]'s [x /\ ~w] gate: the static image is the truth there,
    and a jump into a non-executable segment faults instead of running
    its bytes as code), and assemble them little-endian into a 32-bit
    word.  The w+x counterpart is [fetch_word_ov] below.

    Fetch also returns [None] on a MISALIGNED [addr]: RV64 with the C
    extension has IALIGN=16, so fetching at pc mod 2 <> 0 is an
    instruction-address-misaligned trap — the process observably
    crashes, same as a bad fetch.  (With compressed instructions
    modeled, pc ≡ 2 (mod 4) is a legal fetch address.)  [Sem]
    never produces a misaligned pc from a jump — jal/branch
    immediates are even and jalr clears bit 0 per the spec — so this
    gate covers the one PC source no jump path constrains, a
    misaligned [init_pc] taken verbatim from the ELF [e_entry]. *)
Definition fetch_word (addr : word) : option (bv 32) :=
  if negb (Z.eqb (bv_unsigned addr mod 2) 0)%Z then None
  else
  match code_read addr 4 with
  | Some (b0 :: b1 :: b2 :: b3 :: []) => Some (le4 b3 b2 b1 b0)
  | _ => None
  end.

(** Word fetch from a WRITABLE executable (w+x) segment, through the
    overlay-first view ([code_read_ov]); same alignment gate as
    [fetch_word].  Because the two gates are complementary, at most one
    of [fetch_word]/[fetch_word_ov] can succeed at any address; [step]
    tries [fetch_word] first, so the immutable-code fast path is
    unchanged by the existence of this one. *)
Definition fetch_word_ov (m : word -> option byte) (addr : word)
    : option (bv 32) :=
  if negb (Z.eqb (bv_unsigned addr mod 2) 0)%Z then None
  else
  match code_read_ov m addr 4 with
  | Some (b0 :: b1 :: b2 :: b3 :: []) => Some (le4 b3 b2 b1 b0)
  | _ => None
  end.

(** The STATIC projection of [fetch_word_ov]: the w+x segment's image
    bytes alone ([code_read_wx]).  A pure function of the snapshot, so
    the generated per-example fetch lemmas for a w+x image are stated
    over it and closed by [vm_compute]; [fetch_word_ov] rewrites to it
    whenever the overlay misses the fetched range (Common/WxExec.v). *)
Definition fetch_word_wx (addr : word) : option (bv 32) :=
  if negb (Z.eqb (bv_unsigned addr mod 2) 0)%Z then None
  else
  match code_read_wx addr 4 with
  | Some (b0 :: b1 :: b2 :: b3 :: []) => Some (le4 b3 b2 b1 b0)
  | _ => None
  end.

(** ** Halfword-granular instruction fetch (RVC-correct)

    RISC-V determines an instruction's length from the low bits of its
    FIRST 16-bit parcel: [instr[1:0] <> 0b11] is a 2-byte compressed
    instruction, [instr[1:0] = 0b11] a (here) 4-byte one.  A fetch must
    therefore read ONLY the parcels the instruction actually occupies —
    a compressed instruction in the last two bytes of an executable
    segment (or immediately before a non-executable page) must fetch
    from just those two bytes, never a spurious four-byte read that
    faults on bytes the instruction does not use.

    [fetch_half] reads one aligned 16-bit parcel through [code_read]
    (same 'x' ∧ ¬'w' gate as [fetch_word]).  [fetch_tail] is the
    length-correct fetch: read parcel 0; if it is compressed, that is
    the whole instruction (zero-extended into the 32-bit word the
    decoder consumes — [decode_any] reads only [bits 0 16] for a
    compressed encoding, and the low two bits <> 0b11 keep it clear of
    the ECALL test); if it is a 32-bit instruction, read parcel 1 and
    concatenate.

    [step] uses [fetch_word] as a fast path and falls back to
    [fetch_tail] only when the four-byte read fails — exactly the
    boundary case above.  Reading four bytes when only two are needed is
    harmless under the model's snapshot invariant that loaded segments
    do not overlap (enforced when the memory image is built): the extra
    parcel is either within the same executable segment (readable, so
    the fast path succeeds and the decoder ignores it for a compressed
    instruction) or outside it (so the four-byte read fails and the
    fallback runs).  With overlapping segments the two reads could
    resolve to different segments, so the fast path is NOT a generic
    no-op; the agreement is pinned on representative fixtures in
    [Checks/RiscvCompressedFetch.v] rather than asserted for arbitrary
    segment lists. *)
Definition fetch_half (addr : word) : option (bv 16) :=
  match code_read addr 2 with
  | Some (b0 :: b1 :: []) => Some (le2 b1 b0)
  | _ => None
  end.

Definition fetch_tail (addr : word) : option (bv 32) :=
  if negb (Z.eqb (bv_unsigned addr mod 2) 0)%Z then None
  else
  match fetch_half addr with
  | None => None
  | Some h0 =>
    if (bv_unsigned (bits 0 2 h0) =? 3)%Z then
      (* 32-bit instruction: read the upper parcel too. *)
      match fetch_half (addr + 2) with
      | Some h1 => Some (bv_concat 32 h1 h0)
      | None => None
      end
    else
      (* compressed: two bytes suffice; the upper parcel is decoder-dead. *)
      Some (bv_concat 32 (0 : bv 16) h0)
  end.

(** The w+x halfword fetch, and the COMBINED (either-kind-of-segment)
    halfword and length-correct fetches.  [fetch_half_any] reads a
    16-bit parcel from whichever executable segment holds it — the
    static image for immutable code, the overlay-first view for w+x
    code (the two gates are complementary, so the ordering is
    dispatch, not preference).  [fetch_tail_any] is [fetch_tail]'s
    length-correct algorithm over [fetch_half_any], so each parcel of
    an instruction may independently come from either kind of segment
    (matching hardware, where segment permissions are per page and an
    instruction may straddle a boundary). *)
Definition fetch_half_ov (m : word -> option byte) (addr : word)
    : option (bv 16) :=
  match code_read_ov m addr 2 with
  | Some (b0 :: b1 :: []) => Some (le2 b1 b0)
  | _ => None
  end.

Definition fetch_half_any (m : word -> option byte) (addr : word)
    : option (bv 16) :=
  match fetch_half addr with
  | Some h => Some h
  | None => fetch_half_ov m addr
  end.

Definition fetch_tail_any (m : word -> option byte) (addr : word)
    : option (bv 32) :=
  if negb (Z.eqb (bv_unsigned addr mod 2) 0)%Z then None
  else
  match fetch_half_any m addr with
  | None => None
  | Some h0 =>
    if (bv_unsigned (bits 0 2 h0) =? 3)%Z then
      match fetch_half_any m (addr + 2) with
      | Some h1 => Some (bv_concat 32 h1 h0)
      | None => None
      end
    else
      Some (bv_concat 32 (0 : bv 16) h0)
  end.

(** ** ECALL instruction detector

    RISC-V ECALL encoding is exactly 0x00000073.  (A compressed
    instruction can never alias this test: the low 2 bits of 0x73 are
    11, the uncompressed marker.) *)
Definition is_ecall (w : bv 32) : bool :=
  bv_eqb w (Z_to_bv 32 0x73).

(** ** ISA-semantics integration

    [Sem.exec] maps a decoded instruction and the core state
    ([Sem.core]: integer and FP registers, pc, fcsr, LR/SC
    reservation) to a finite first-order EFFECT TREE whose nodes are
    the operations the semantics does not interpret itself.  This
    section supplies the interpreter: [ELoad]s read through the
    writable overlay with segment fallback and fail on any unmapped
    byte; [EStore]s fail on any range with a byte outside the
    writable view ([store_ok] — the SIGSEGV analogue); the boundary
    nodes [EIllegal]/[EDefinedIllegal]/[EEcall]/[EEbreak] all map to
    failure (ebreak is
    fatal here, and ECALL is intercepted BEFORE decode by [step], so
    [EEcall] is unreachable anyway), split between [MachineFault] and
    [MachineUnmodeled] as described at [interp_eff].  A failed interpretation propagates
    unchanged through [step].

    The machine's register files [ms_regs]/[ms_fregs] are
    [bvmap 5 word]s — the SAME representation as [Sem.core]'s
    [c_regs]/[c_fregs] — so [step] passes them into [exec] and
    projects them back verbatim, with no conversion in either
    direction; [ms_fcsr] is likewise [Sem.core]'s [c_fcsr]
    unchanged. *)

(** Byte counts for the [ELoad]/[EStore] widths (which are in BITS:
    8/16/32/64).  Total by construction; other widths never occur. *)
Definition width_bytes (n : N) : nat :=
  match n with
  | 8%N => 1 | 16%N => 2 | 32%N => 4 | 64%N => 8
  | _ => 0
  end.

Definition width_bytesZ (n : N) : Z :=
  match n with
  | 8%N => 1 | 16%N => 2 | 32%N => 4 | 64%N => 8
  | _ => 0
  end%Z.

(** *** Overlay-then-segments memory read

    Read [n] bytes starting at [addr]: each byte comes from the
    writable overlay if present, else from the loaded segments; fail
    on any miss. *)
Fixpoint ov_read_bytes (m : word -> option byte) (addr : word) (n : nat)
    : option (list byte) :=
  match n with
  | O => Some []
  | S n' =>
    match (match m addr with
           | Some b => Some b
           | None => match memory_read addr 1 with
                     | Some (b :: _) => Some b
                     | _ => None
                     end
           end) with
    | Some b =>
      match ov_read_bytes m (addr + 1) n' with
      | Some rest => Some (b :: rest)
      | None => None
      end
    | None => None
    end
  end.

(** *** Memory accesses reported by the tree interpreter

    A successful instruction reports every data-memory range it accessed.
    The report is separate from [machine_state]: it is an observation of one
    step, not architectural state.  A caller can therefore inspect accesses
    without adding an observation field to every machine-state literal in the
    development.  A range is reported only after its load or store permission
    check succeeds.  The complete list is returned with the successful
    instruction, so a consumer can validate all ranges atomically before
    accepting the transition. *)
Definition memory_access := (word * nat)%type.

Record access_report (A : Type) := mkAccessReport {
  access_value : A;
  accessed_ranges : list memory_access;
}.

Arguments mkAccessReport {A}.

Definition drop_access_report {A} (r : machine_result (access_report A))
    : machine_result A :=
  match r with
  | MachineOk report => MachineOk (@access_value A report)
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.

(** *** The tree interpreter

    Structural recursion over the effect tree; the writable overlay
    is threaded through.  [ELoad n a k]'s continuation receives the
    [width_bytes n] loaded bytes assembled little-endian ([n] is the
    access width in bits); [EStore n a v k] writes the [width_bytes n]
    little-endian bytes of [v] into the overlay, but only once every
    byte of the range is known writable ([store_ok]).  The boundary
    nodes are all terminal
    failures, but of the two DIFFERENT kinds (see [machine_result]):

    - [EEbreak] is a [MachineFault] — a real process takes SIGTRAP and
      dies, so the model is faithful here;
    - [EFault] is a [MachineFault] — the ISA itself defines the
      execution to trap (today: a misaligned lr/sc/amo, the SIGBUS
      analogue; see [Sem.amo_aligned]), so this is the process
      crashing, not the model declining;
    - a failed [ELoad] (unmapped byte) and a failed [EStore] (any byte
      of the range outside the writable view — a non-writable segment,
      or memory that was never mapped at all; see [store_ok]) are
      [MachineFault]s too: the SIGSEGV analogue;
    - [EIllegal] is [MachineUnmodeled] — the ISA semantics declined to
      give this instruction a meaning (an unknown CSR address, or a
      reserved FP rounding mode).  [EEcall] is unreachable (ECALL is
      intercepted before decode in [step]) and is classified
      [MachineUnmodeled] with the rest of the boundary;
    - [EDefinedIllegal] is a [MachineFault] — the ARCHITECTURE, not this
      model, defines the instruction to raise an illegal-instruction
      exception (today: a write to a read-only CSR address, which is what
      GNU as's [unimp] and hence every fired -fsanitize-trap check is),
      so the process takes SIGILL and dies.  This is the same split
      [EFault]/[EIllegal] draw, one level up: see [Sem.csr_write_illegal]
      for why the address alone settles it. *)
Fixpoint interp_eff_accesses (t : eff) (m : word -> option byte)
    : machine_result (access_report (core * (word -> option byte))) :=
  match t with
  | EDone c => MachineOk (mkAccessReport (c, m) [])
  | EEbreak _ | EFault _ | EDefinedIllegal _ => MachineFault
  | EIllegal _ | EEcall _ => MachineUnmodeled
  | ELoad n a k =>
      match ov_read_bytes m a (width_bytes n) with
      | Some bs =>
        match interp_eff_accesses
                (k (bv_extract 0 n (le_bytes_to_word bs))) m with
        | MachineOk report =>
          MachineOk
            (mkAccessReport (@access_value _ report)
               ((a, width_bytes n) :: @accessed_ranges _ report))
        | MachineFault => MachineFault
        | MachineUnmodeled => MachineUnmodeled
        end
      | None => MachineFault
      end
  | EStore n a v k =>
      if store_ok m a (width_bytes n)
      then
        match interp_eff_accesses k
                (write_to_mem m a
                   (Z_to_le_bytes (width_bytes n) (bv_unsigned v))) with
        | MachineOk report =>
          MachineOk
            (mkAccessReport (@access_value _ report)
               ((a, width_bytes n) :: @accessed_ranges _ report))
        | MachineFault => MachineFault
        | MachineUnmodeled => MachineUnmodeled
        end
      else MachineFault
  end.

(** There is one trusted interpreter.  Callers that do not need access
    observations project them away from its result. *)
Definition interp_eff (t : eff) (m : word -> option byte)
    : machine_result (core * (word -> option byte)) :=
  drop_access_report (interp_eff_accesses t m).

(** Erasing an access report recovers the authoritative architectural
    interpreter exactly.  This is the bridge used by the existing symbolic
    proof library: access accounting adds an observation, never a second ISA
    semantics. *)
Lemma drop_interp_eff_accesses : forall t m,
  drop_access_report (interp_eff_accesses t m) = interp_eff t m.
Proof.
  reflexivity.
Qed.

(** ** Decode-and-execute a fetched instruction word

    Given the 32-bit word [w] the fetch produced (a full 32-bit
    encoding, or a compressed 16-bit encoding zero-extended into the low
    parcel — see [fetch_tail]):

    1. Check if the word is [ecall] (Linux riscv64 syscall boundary).
       If yes: record [ms_reg st 17] (a7) as the pending syscall number.
    2. Otherwise: decode ([DecodeC.decode_any], 32-bit or compressed),
       build the effect tree ([Sem.exec]) and interpret it
       ([interp_eff]).  The core is built from the machine state with
       both register maps and fcsr passed through UNCHANGED
       ([ms_regs]/[ms_fregs] and [c_regs]/[c_fregs] share the [bvmap]
       representation) and projected back the same way.
    3. On decode failure: [MachineUnmodeled], fail closed — an
       undecodable word may be a genuinely illegal encoding, but it
       may equally be a hole in THIS decoder, and the two are not in
       general distinguishable from here.  The one exception is a word
       the architecture pins as illegal in every implementation:
       [DecodeC.is_defined_illegal] (today, exactly the all-zero low
       parcel), where real hardware is guaranteed to trap and Linux
       delivers SIGILL — the process dies there too, so that word is a
       [MachineFault], per the classification rule on
       [machine_result].  A DECODABLE instruction can be defined-illegal
       too, and that decision belongs to [Sem.exec] rather than here: it
       answers [Sem.EDefinedIllegal], which [interp_eff] faults on.  On
       interpretation failure:
       whichever of [MachineFault]/[MachineUnmodeled] [interp_eff]
       reports.  Either way the trace semantics turns it into the
       explicit error transition; only [MachineUnmodeled] additionally
       marks the configuration as one the model failed to cover. *)
Definition decode_exec_accesses (st : machine_state) (w : bv 32)
    : machine_result (access_report machine_state) :=
  if is_ecall w then
    MachineOk (mkAccessReport
      {| ms_regs := ms_regs st; ms_fregs := ms_fregs st;
         ms_pc_val := ms_pc_val st;
         ms_svc_pending := Some (ms_reg st 17);
         ms_resv := ms_resv st; ms_fcsr := ms_fcsr st;
         ms_mem := st.(ms_mem);
         ms_rom := st.(ms_rom) |} [])
  else
    match decode_any w with
    | None =>
      if is_defined_illegal w then MachineFault else MachineUnmodeled
    | Some (i, isz) =>
      match interp_eff_accesses (exec (Z_to_bv 64 isz) i
                           {| c_regs := st.(ms_regs);
                              c_fregs := st.(ms_fregs);
                              c_pc := st.(ms_pc_val);
                              c_fcsr := st.(ms_fcsr);
                              c_resv := st.(ms_resv) |})
                        st.(ms_mem) with
      | MachineFault => MachineFault
      | MachineUnmodeled => MachineUnmodeled
      | MachineOk report =>
        let '(c, m') := @access_value _ report in
        MachineOk (mkAccessReport
          {| ms_regs := c.(c_regs); ms_fregs := c.(c_fregs);
             ms_pc_val := c.(c_pc);
             ms_svc_pending := None;
             ms_resv := c.(c_resv); ms_fcsr := c.(c_fcsr);
             ms_mem := m';
             ms_rom := st.(ms_rom) |}
          (@accessed_ranges _ report))
      end
    end.

Definition decode_exec (st : machine_state) (w : bv 32)
    : machine_result machine_state :=
  drop_access_report (decode_exec_accesses st w).

(** ** Step function

    Fetch the instruction at [ms_pc st] and hand its word to
    [decode_exec].  The fetch takes the fast path first: a single
    four-byte [fetch_word] from immutable code.  If that fails it tries
    the four-byte w+x fetch [fetch_word_ov] (the complementary gate:
    exactly one of the two can apply to any address).  If that fails
    too — the interesting cases being a compressed instruction whose
    second parcel lies outside the fetchable segment, a boundary a
    four-byte read cannot cross, or an instruction straddling two
    abutting executable segments — it retries with the length-correct
    combined halfword fetch [fetch_tail_any] (see the [fetch_tail] note
    for why the fast path is sound under the non-overlap snapshot
    invariant).

    A failed fetch is classified by WHY it failed, via [fetch_failure]:
    a misaligned PC, or a needed byte that is unmapped or
    non-executable, is a [MachineFault] — a wild jump is a crash, NOT a
    clean exit, and it is a crash the real
    process suffers too, so it is modeled.  A needed byte the fetch
    declined for the MODEL's own reasons (snapshot hex the decoder
    cannot read, or a read straddling abutting segments that
    [find_segment] declines) is a [MachineUnmodeled] instead. *)

(** Classify a fetch at [addr] that every fetch path declined.  A
    misaligned pc is a genuine instruction-address-misaligned trap.
    Otherwise inspect exactly the bytes the instruction needs — parcel 0
    always, and parcel 1 only when parcel 0 was readable and announced a
    32-bit encoding, which is the only remaining way [fetch_tail_any]
    can fail — and report [MachineFault] if any of them would trap on
    real hardware.  If none would, the decline was this model's own
    ([MachineUnmodeled]). *)
Definition fetch_failure (m : word -> option byte) (addr : word)
    : machine_result machine_state :=
  if negb (Z.eqb (bv_unsigned addr mod 2) 0)%Z then MachineFault
  else
    let traps :=
      (fetch_byte_traps addr || fetch_byte_traps (addr + 1)
       || match fetch_half_any m addr with
          | None => false           (* parcel 0 is mapped and executable *)
          | Some _ =>               (* ...so the failure is in parcel 1 *)
            (fetch_byte_traps (addr + 2) || fetch_byte_traps (addr + 3))%bool
          end)%bool in
    if traps then MachineFault else MachineUnmodeled.

Definition step_accesses (st : machine_state)
    : machine_result (access_report machine_state) :=
  match fetch_word (ms_pc st) with
  | Some w => decode_exec_accesses st w
  | None =>
    match fetch_word_ov st.(ms_mem) (ms_pc st) with
    | Some w => decode_exec_accesses st w
    | None =>
      match fetch_tail_any st.(ms_mem) (ms_pc st) with
      | Some w => decode_exec_accesses st w
      | None =>
        match fetch_failure st.(ms_mem) (ms_pc st) with
        | MachineOk st' => MachineOk (mkAccessReport st' [])
        | MachineFault => MachineFault
        | MachineUnmodeled => MachineUnmodeled
        end
      end
    end
  end.

Definition step (st : machine_state) : machine_result machine_state :=
  drop_access_report (step_accesses st).

Lemma drop_decode_exec_accesses : forall st w,
  drop_access_report (decode_exec_accesses st w) = decode_exec st w.
Proof.
  reflexivity.
Qed.

Lemma drop_step_accesses : forall st,
  drop_access_report (step_accesses st) = step st.
Proof.
  reflexivity.
Qed.

End WithMemImage.

Global Strategy 100
  [step step_accesses decode_exec decode_exec_accesses
   drop_access_report interp_eff_accesses
   memory_read code_read code_read_wx code_read_ov
   seg_ov_read_bytes fetch_word fetch_word_ov fetch_word_wx fetch_tail
   fetch_half fetch_half_ov fetch_half_any fetch_tail_any
   fetch_failure fetch_byte_traps interp_eff store_ok wview].
