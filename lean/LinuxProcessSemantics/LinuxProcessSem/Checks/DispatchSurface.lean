import LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit
import LinuxProcessSemantics.LinuxProcessSem.StackLayout

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570
unported: listed_once -- Rocq counts occurrences with `Z.eqb` so that `vm_compute` does not normalise the equality proofs `count_occ Z.eq_dec` carries, and bridges the two symbolically; Lean's `List.Nodup` is decided directly by `modeled_sysnos_nodup`, so there is nothing to bridge -/

/-! # LinuxProcessSem.Checks.DispatchSurface — the modeled surface, both directions

Mirrors `theories/LinuxProcessSem/Checks/DispatchSurface.v` at the header's
baseline, where the Rocq file is byte-identical to `f44244ad6b80`, the
commit the ticket names, with the epoll probe using an answering input
on Lean's narrower Lean surface. Not part of the trusted specification.

Two directions relate `Specs.modeled_sysnos` to what `Specs.syscall_spec`
answers.  Direction 1, that an answer means the number is listed and a
number outside the list means the decline, needs nothing of any table but
`spec_table` itself.  Direction 2, that every listed number is answered
somewhere, needs a witness for each number, and Rocq takes it from
`Progress.syscall_spec_witness` on a fixed probe input per number.

## Where direction 1 is

`lookup_arm_in`, `syscall_spec_number_modeled`, `syscall_spec_unmodeled_outside`
and the no-repeats check `modeled_sysnos_nodup` landed in
`Checks/Examples.lean` ahead of this twin, which that file's prose says.
They are used from there rather than restated, because a second theorem of
the same name over the same table is a second thing for a reader to compare.
Moving them here touches a file outside this ticket's, and
`Checks/Sys/Table.lean`'s header names `Checks/Examples.lean` as
`modeled_sysnos_nodup`'s home, so the move is a `lean: base:` change of its
own; until it lands the twin is split across the two files.  The one direction-1 theorem Rocq states after those three,
`syscall_spec_declines_outside`, is here.

## What the partial table does to direction 2

Rocq's `modeled_sysnos_probes_answer` computes `probe_answers` over every
listed number and requires `true`: a number given an arm and no answering
probe fails the build.  Its witness is `syscall_spec_witness`, which reads
`checked_table`, and the Lean `checked_table` is partial while the Track C
tickets land, so the witness is the decline at every number the checked
table lacks — at which the Rocq statement is simply false today.  The Lean
check is therefore stated over the CHECKED numbers,
`checked_sysnos_probes_answer`, which grows with the table and fails the
build the day a checked arm declines its probe; Rocq's statement follows
from it once the table is complete (`modeled_sysnos_probes_answer_of_complete`).
`modeled_sysnos_dispatched` and `modeled_sysnos_exact` carry the same
hypothesis `Checks/Progress.lean` carries — the two tables agree at the
number — with the checked-number form, and the complete-table form that
retires the hypothesis, beside each. The Lean-specific probe fixtures
are explained beside `probe_args`,
and the reasons for each entry are in the Rocq file beside them; they are
not repeated here, since a reason that is not checked is one that
drifts.  Where a Lean twin lacks a constant Rocq has, the probe spells the
value and says so at the spot.

The register above takes definitions.  Rocq's lemmas `forallb_In`,
`in_of_existsb_eqb`, `count_occ_filter_eqb`, `nodup_of_listed_once` and
`modeled_sysnos_listed_once` are proof-internal, and the Lean proofs do
not need them. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.DispatchSurface

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout (hwcap_rv64gc)
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork (SIGCHLD CLONE_ARGS_SIZE)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit (WAIT_ANY32)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples

/-! ## Direction 1: outside the list, the decline is admitted

Rocq derives this from `syscall_spec_unmodeled_outside` and `receptive` in
two steps.  The Lean `receptive` carries a hypothesis, and the theorem does
not need it: a number with no arm reaches the dispatcher's own final
`unmodeled`, which `Sys.Dispatch.dispatch_unmodeled` states, so the proof
reads the table rather than the witness. -/

theorem syscall_spec_declines_outside (i : SyscallInput) (m : Model)
    (hn : bv_unsigned i.in_sysno ∉ modeled_sysnos) : syscall_spec i m Unmodeled := by
  have hnone : lookup_arm spec_table (bv_unsigned i.in_sysno) = none := by
    cases h : lookup_arm spec_table (bv_unsigned i.in_sysno) with
    | none => rfl
    | some a => exact absurd (lookup_arm_in spec_table _ a h) hn
  exact dispatch_unmodeled spec_table i m hnone

/-! ## Direction 2: the probe fixtures

Rocq's, name for name.  The declared-abort exception to the default model
is Rocq's too: `tkill` (130) and `tgkill` (131) answer only under the
task's declaration of the abort path and only for the caller's own tid,
so their probe runs against `probe_model_abort`, which declares it and
pins a tid. The mremap probe also needs a tracked source for a grow. -/

def probe_model : Model :=
  init_model [] (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 sp_window_lo) 0x40000000
    (ProcInput.mkProcInput [] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
      net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false .Sv48)

def probe_tid : word := Z_to_bv 64 4242

def probe_model_abort : Model :=
  with_tid probe_tid
    (init_model [] (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 sp_window_lo) 0x40000000
      (ProcInput.mkProcInput [] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
        net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc true .Sv48))

/-- The model a probe of `n` runs against. -/
def probe_model_for (n : Int) : Model :=
  if n = 130 || n = 131 then probe_model_abort
  else if n = 216 then
    with_vmmaps (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 8192 0 (Z_to_bv 64 sp_window_lo)) probe_model
  else probe_model

/-- Where `clone3`'s probe finds a fork-shaped `struct clone_args`. -/
def clone3_probe_uargs : word := Z_to_bv 64 0x10000

/-- Every address readable and writable and holding a NUL byte, except the
one that makes `clone3`'s struct fork-shaped: `exit_signal` is the fifth
`__aligned_u64` of `struct clone_args` (`include/uapi/linux/sched.h`,
Linux v6.18.46, commit 1f99e9ab748f), at offset 32, and the fork shape
the arm admits has it equal to `SIGCHLD` and every other field zero. -/
def probe_mem : word → Option byte :=
  fun a => some (if bv_eqb a (clone3_probe_uargs + Z_to_bv 64 32)
                 then Z_to_bv 8 SIGCHLD
                 else Z_to_bv 8 0)

/-- Arguments for the probe of syscall number `n`. Rocq's table with the
Lean-specific probes explained below; the reason each other entry exists is in the Rocq file
beside it.
`sendto` (206) and `sendmsg` (211) carry `MSG_NOSIGNAL`, which is `0x4000`
in `include/linux/socket.h` (Linux v6.18.46, commit 1f99e9ab748f); the
Lean `Sys/Uapi/Net.lean` does not define the constant yet
(`Sys/Net/Socket.lean` registers it), so the two entries spell the value.
The day the constant lands, the two numerals become it and the pin on them
in `Checks/Cases/Checks/DispatchSurface.lean` is what holds the value
meanwhile.

The entry for `ppoll` (73) departs from Rocq's
(`[AT_FDCWD; z; AT_FDCWD; z; z; z]`): Rocq's `ppoll_core` answers 0 for
`nfds = 0` whatever `ufds` is, while the Lean twin declines `nfds = 0`
with a `ufds` that fails `access_okb` (`Sys/Fs/Select.lean`'s
`ppoll_core`; bugs/ppoll-nfds-zero-answers-a-kernel-space-ufds.md), and
`AT_FDCWD` as an address is above `TASK_SIZE`.  So `a0` is NULL, which
`__access_ok` (include/asm-generic/access_ok.h:31-41, Linux v6.18.46,
commit 1f99e9ab748f) passes at size 0, and the probe is answered 0.
`a2` keeps the timeout pointer.

For ioctl (29), request 0 is declined before fd lookup by the fd-first
gate. TIOCGWINSZ lets the closed descriptor reach EBADF.
For epoll_ctl (21), raw DEL (2) makes both implementations ignore the
event pointer and reach the closed epfd. The default non-DEL operation
disagrees because probe_mem defines bytes even at NULL.
For epoll_pwait (22), Lean declines the closed-fd/count-one fixture when
QEMU can answer differently. A nonnull mask with size zero gives Linux
EINVAL before fd lookup; count zero gives QEMU the same answer. -/
def probe_args (n : Int) : List word :=
  let z := Z_to_bv 64 0
  if n = 29 then [AT_FDCWD, TIOCGWINSZ, z, z, z, z]
  else if n = 19 then [z, Z_to_bv 64 O_LARGEFILE, z, z, z, z]
  else if n = 21 then [AT_FDCWD, Z_to_bv 64 2, z, z, z, z]
  else if n = 22 then [AT_FDCWD, z, z, z, Z_to_bv 64 1, z]
  -- Count one keeps these closed-fd witnesses outside the parameter-order declines.
  else if n = 65 || n = 66 then [AT_FDCWD, z, Z_to_bv 64 1, z, z, z]
  -- T139/#1441: op 0 on the closed probe fd has version-dependent
  -- errno precedence; LOCK_EX keeps the universally shared EBADF answer.
  else if n = 32 then [AT_FDCWD, Z_to_bv 64 LOCK_EX, z, z, z, z]
  else if n = 222 then [AT_FDCWD, z, z, Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS), z, z]
  else if n = 216 then [65536, 4096, 8192, Z_to_bv 64 MREMAP_MAYMOVE, z, z]
  else if n = 261 then [z, Z_to_bv 64 RLIMIT_CORE, z, Z_to_bv 64 4096, z, z]
  else if n = 199 then [Z_to_bv 64 AF_INET, Z_to_bv 64 SOCK_STREAM, z, z, z, z]
  else if n = 113 then [Z_to_bv 64 CLOCK_REALTIME, z, z, z, z, z]
  else if n = 98 then [z, Z_to_bv 64 FUTEX_WAKE_PRIVATE, z, z, z, z]
  else if n = 167 then [Z_to_bv 64 PR_CAPBSET_READ, z, z, z, z, z]
  else if n = 220 then [Z_to_bv 64 SIGCHLD, z, z, z, z, z]
  else if n = 435 then [clone3_probe_uargs, Z_to_bv 64 CLONE_ARGS_SIZE, z, z, z, z]
  else if n = 260 then [Z_to_bv 64 WAIT_ANY32, z, Z_to_bv 64 WNOHANG, z, z, z]
  else if n = 132 then [z, z, z, z, z, z]
  else if n = 206 then [AT_FDCWD, z, z, Z_to_bv 64 0x4000, z, z]
  else if n = 73 then [z, z, AT_FDCWD, z, z, z]
  else if n = 130 then [probe_tid, Z_to_bv 64 SIGABRT, z, z, z, z]
  else if n = 131 then [probe_tid, probe_tid, Z_to_bv 64 SIGABRT, z, z, z]
  else if n = 211 then [AT_FDCWD, z, Z_to_bv 64 0x4000, z, z, z]
  else [AT_FDCWD, z, z, z, z, z]

def probe_input (n : Int) : SyscallInput :=
  SyscallInput.mkInput (Z_to_bv 64 n) (probe_args n) probe_mem probe_mem

/-- Whether the arms of a table `t` answer the probe of `n`.  Lean-only:
Rocq's `probe_answers` reads `syscall_spec_witness`, which is this at
`checked_table`; the table is a parameter so that the check below can be
run on the fixture tables. -/
def probe_answers_in (t : List CheckedArm) (n : Int) : Bool :=
  match table_witness t (probe_input n) (probe_model_for n) with
  | Ok _ _ _ => true
  | Unmodeled => false

def probe_answers (n : Int) : Bool := probe_answers_in checked_table n

/-- An answer read off `probe_answers_in` IS the table's witness being an
answer: the decline is the one witness the function maps to `false`. -/
theorem probe_answers_in_eq_false_of_unmodeled (t : List CheckedArm) (n : Int)
    (h : table_witness t (probe_input n) (probe_model_for n) = Unmodeled) :
    probe_answers_in t n = false := by
  unfold probe_answers_in
  rw [h]

/-! ## THE CHECK

Rocq: `modeled_sysnos_probes_answer`, over `modeled_sysnos`.  Here over the
numbers the checked table carries, for the reason the header gives: the
witness at a number the checked table lacks is the decline, whatever the
spec arm there would answer.  A checked arm whose witness declines its
probe turns this into `false = true`, and the fix is the arm's witness or
a `probe_args` entry, as in Rocq.  When the checked table is complete the
two statements coincide, and `modeled_sysnos_probes_answer_of_complete`
says so.

Which numbers the checked table carries is a fact about its contents,
and no sentence here states it: over the table K2 left, which holds no
arm, the `all` runs over no number and the theorem is decided vacuously,
and each C ticket's arm puts its probe under it as it lands.  Until then
the fixture-table pins in `Checks/Cases/Checks/DispatchSurface.lean` are
what show the check failing a declining arm.

`decide` evaluates each checked witness on its probe.  Should an arm's
witness be one Meta's evaluator does not reduce — the `Nat.sub`-on-literal
shape `docs/lean-port` records for the `Int` gates — the kernel's
evaluator still does, and the proof becomes `decide +kernel` with the
reason recorded here; nothing else about the statement moves. -/

theorem checked_sysnos_probes_answer :
    (checked_table.map ca_no).all probe_answers = true := by decide

/-- Rocq's statement, at the complete table. -/
theorem modeled_sysnos_probes_answer_of_complete
    (hall : checked_table.map CheckedArm.ca_arm = spec_table) :
    modeled_sysnos.all probe_answers = true := by
  have h : modeled_sysnos = checked_table.map ca_no := by
    unfold modeled_sysnos arm_numbers
    rw [← hall, List.map_map]
    rfl
  rw [h]
  exact checked_sysnos_probes_answer

/-! ## The listed numbers fit a syscall register

Rocq's `modeled_sysnos_in_range`, stated through a named predicate so that
the theorem carries no numeral: `tools/check_decline_registers.py` reads
every statement that names `modeled_sysnos` beside an integer literal as a
decline register and refuses the ones it cannot classify. -/

/-- `0 ≤ n < 2^64`: the number fits the 64-bit register it arrives in —
`a7` on riscv64, the word `Run.sstep` reads out of `ms_svc_pending`. -/
def sysno_in_range (n : Int) : Bool := decide (0 ≤ n) && decide (n < 2 ^ 64)

theorem sysno_in_range_iff (n : Int) : sysno_in_range n = true ↔ 0 ≤ n ∧ n < 2 ^ 64 := by
  simp only [sysno_in_range, Bool.and_eq_true, decide_eq_true_eq]

theorem modeled_sysnos_in_range : modeled_sysnos.all sysno_in_range = true := by decide

/-- Stated through the predicate rather than its two bounds, for the reason
the section header gives. -/
theorem modeled_sysno_in_range (n : Int) (hn : n ∈ modeled_sysnos) : sysno_in_range n = true :=
  List.all_eq_true.mp modeled_sysnos_in_range n hn

/-- The probe of a listed number carries that number: `Z_to_bv` round-trips
on a value the register holds. -/
theorem probe_input_sysno (n : Int) (hn : n ∈ modeled_sysnos) :
    bv_unsigned (probe_input n).in_sysno = n := by
  obtain ⟨h0, h1⟩ := (sysno_in_range_iff n).mp (modeled_sysno_in_range n hn)
  exact bv_unsigned_Z_to_bv_small n h0 h1

/-! ## Direction 2: every listed number is answered somewhere

The general form takes any table whose arms the dispatcher vouches for
(`Checks.Sys.Table.arms_agree`) and whose checked numbers all answer their
probe, and produces the answer for a number the table carries.
`checked_sysnos_dispatched` is its instance at `checked_table`, whose two
premises are `checked_table_arms` and `checked_sysnos_probes_answer`;
Rocq's `modeled_sysnos_dispatched` is then the instance at a listed number
where the two tables agree, which is where the hypothesis
`Checks/Progress.lean` carries enters, and the complete-table form retires
it. -/

theorem sysnos_dispatched_over (t : List CheckedArm) (ht : arms_agree t)
    (hprobe : (t.map ca_no).all (probe_answers_in t) = true)
    (n : Int) (c : CheckedArm) (hc : lookup_ca t n = some c) :
    ∃ i m o, bv_unsigned i.in_sysno = n ∧ syscall_spec i m o ∧ o ≠ Unmodeled := by
  have hmem : c ∈ t := lookup_ca_In t n c hc
  have hno : ca_no c = n := lookup_ca_no t n c hc
  have hlisted : n ∈ modeled_sysnos := by
    rw [← hno]
    exact lookup_arm_in spec_table (ca_no c) c.ca_arm (ht c hmem)
  have hn : bv_unsigned (probe_input n).in_sysno = n := probe_input_sysno n hlisted
  have hans : probe_answers_in t n = true :=
    List.all_eq_true.mp hprobe n (List.mem_map.mpr ⟨c, hmem, hno⟩)
  refine ⟨probe_input n, probe_model_for n,
    table_witness t (probe_input n) (probe_model_for n), hn, ?_, ?_⟩
  · apply receptive_checked_over t ht (probe_input n) (probe_model_for n) c
    rw [hn]
    exact hc
  · intro ho
    rw [probe_answers_in_eq_false_of_unmodeled t n ho] at hans
    exact Bool.false_ne_true hans

/-- Every number the checked table carries is answered on its probe. -/
theorem checked_sysnos_dispatched (n : Int) (c : CheckedArm)
    (hc : lookup_ca checked_table n = some c) :
    ∃ i m o, bv_unsigned i.in_sysno = n ∧ syscall_spec i m o ∧ o ≠ Unmodeled :=
  sysnos_dispatched_over checked_table checked_table_arms checked_sysnos_probes_answer n c hc

/-- Rocq: `modeled_sysnos_dispatched`, under agreement of the two tables at
the number.  Agreement at a listed number puts an arm for it in the checked
table, and that arm answers the probe. -/
theorem modeled_sysnos_dispatched (n : Int) (hn : n ∈ modeled_sysnos)
    (hagree : lookups_agree_at n) :
    ∃ i m o, bv_unsigned i.in_sysno = n ∧ syscall_spec i m o ∧ o ≠ Unmodeled := by
  obtain ⟨a, ha⟩ := in_lookup_arm spec_table n hn
  have h : (lookup_ca checked_table n).map CheckedArm.ca_arm = some a := by
    unfold lookups_agree_at lookups_agree_in at hagree
    rw [← hagree]
    exact ha
  cases hc : lookup_ca checked_table n with
  | none =>
    rw [hc] at h
    cases h
  | some c => exact checked_sysnos_dispatched n c hc

theorem modeled_sysnos_dispatched_of_complete
    (hall : checked_table.map CheckedArm.ca_arm = spec_table)
    (n : Int) (hn : n ∈ modeled_sysnos) :
    ∃ i m o, bv_unsigned i.in_sysno = n ∧ syscall_spec i m o ∧ o ≠ Unmodeled :=
  modeled_sysnos_dispatched n hn (lookups_agree_at_of_complete hall n)

/-- The backward half of `modeled_sysnos_exact`, which needs no
hypothesis: direction 1's `syscall_spec_number_modeled` read at an answer.
Lean-only as a theorem of its own, so that a reader with an answer in hand
does not have to discharge the forward half's hypothesis to use it. -/
theorem modeled_sysnos_of_dispatched (n : Int)
    (h : ∃ i m o, bv_unsigned i.in_sysno = n ∧ syscall_spec i m o ∧ o ≠ Unmodeled) :
    n ∈ modeled_sysnos := by
  obtain ⟨i, m, o, hn, hspec, ho⟩ := h
  cases o with
  | Ok x m' evs =>
    subst hn
    exact syscall_spec_number_modeled i m x m' evs hspec
  | Unmodeled => exact absurd rfl ho

/-- Rocq: `modeled_sysnos_exact`.  The list is exactly the set of numbers
the dispatcher answers; only the forward half carries the hypothesis. -/
theorem modeled_sysnos_exact (n : Int) (hagree : lookups_agree_at n) :
    n ∈ modeled_sysnos ↔
      ∃ i m o, bv_unsigned i.in_sysno = n ∧ syscall_spec i m o ∧ o ≠ Unmodeled :=
  ⟨fun hn => modeled_sysnos_dispatched n hn hagree, modeled_sysnos_of_dispatched n⟩

theorem modeled_sysnos_exact_of_complete
    (hall : checked_table.map CheckedArm.ca_arm = spec_table) (n : Int) :
    n ∈ modeled_sysnos ↔
      ∃ i m o, bv_unsigned i.in_sysno = n ∧ syscall_spec i m o ∧ o ≠ Unmodeled :=
  modeled_sysnos_exact n (lookups_agree_at_of_complete hall n)

end LinuxProcessSemantics.LinuxProcessSem.Checks.DispatchSurface
