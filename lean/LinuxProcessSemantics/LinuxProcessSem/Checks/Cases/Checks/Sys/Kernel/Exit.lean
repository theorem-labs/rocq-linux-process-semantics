import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Exit
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Exit
import LinuxProcessSemantics.LinuxProcessSem.Checks.ProcessCreation

/-! # Checks.Cases.Checks.Sys.Kernel.Exit — the exit and wait4 checkers, exercised

Pins over `Checks.Sys.Kernel.Exit`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Kernel/Exit.v` and
`theories/LinuxProcessSem/Checks/Witness/Kernel/Exit.v`, and over their
`Checks/Sys/Table.lean` arms.  The wait4 dispatcher pins exercise the
registered arm as well as the checker and witness directly.
Not part of the trusted specification.

Rocq has no Cases file for its exit checker.  Its
dispatcher-level claims about exit are the `exit_dispatch_*` lemmas of
`theories/LinuxProcessSem/Checks/Examples.v`, stated over `syscall_spec`,
the spec dispatcher, and twinned as such in `Checks/Examples.lean`; none
of them offers the executable checker an effect.  The wait4 half below
also twins three Rocq claims stated over `check_syscall`.

WHAT IS UNDER TEST is the ACCEPTOR, not the spec.
`Checks/Cases/Kernel/Exit.lean` already reads `exit_spec` off
`kernel/exit.c`, and the four proofs in the checker's file tie
`check_exit` to that spec at every input.  What those proofs cannot say
is which concrete answer the checker gives — a checker that accepted
everything and a spec that admitted everything would satisfy all four —
so each pin here offers the checker one concrete effect and pins the
verdict.  Every accepting pin is paired with the refusal of a different
return or a different halt, so that "the model accepts this" is not the
vacuous reading of a checker that accepts everything.

THE MODEL IS ARBITRARY.  `check_exit` reads nothing off the model, so
every pin is stated over a variable `m`, which is a stronger statement
than one over a fixture and costs nothing.  Where the two sides of an
accepted `with_halted` are the same term the pin is `rfl`; where the
pin's point is the VALUE of the halt — 256 masked to 0, `a0` rather than
`a1` — the bitvector equation is `decide`d on its own and carried across
by `congrArg`, so the arithmetic the pin asserts is the one line a reader
checks.

THE PROBE.  `testing/syscall-check/tests/exit_status.c` runs both
syscalls at a low, a high, a wide and a negative code — the wide one,
`0x100000001ff`, carries a bit beyond `int` — and two `reject --mutate
…:ret=1` cases, all recorded under `testing/syscall-check/traces/`.  The
conforming runs back the `probe:` lines of the wide pins below.  The
refusals here cannot cite the reject cases: `tools/check_lean_pin_evidence.py`
classes a `= CheckReject` statement as positive (the reading
`Checks/Cases/Checks/Sys/Fs/Select.lean`'s header records), so those pins
carry kernel readings instead.  No CASE line of that probe lies about a
ledger although every ledger operator reaches the terminal arm; the
`smuggle-*` reject cases are owed to a `testing: syscall-check:` PR.

WHAT IS NOT PINNED HERE.  The ledger obligation, `arm_exit_preserves_vm`
and its `exit_group` twin, stated in `Checks/Arms/Kernel/Exit.lean`, is
held before the build: `tools/gen_lean_checked.py` refuses an arm file
missing either fact (its ARM-3), and the generated `Checks.Cases.CheckedTable` pins each fact's
type, so a pin here would restate both.

The paragraphs above are the `exit` half's, and `check_exit` reads
nothing off the model.  The `wait4` half, C-Kernel-Exit's, follows
`end K6a` below its sentinel line (BRIEF.md section 4) with a reading
of its own, because `check_wait4` DOES read the model — its children
gate — so its answer and lie pins are stated on the fixture
`demo_model` (and on `with_children` of it), while its gate pins, like
the exit pins, take a variable `m`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Exit

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Exit
open LinuxProcessSemantics.LinuxProcessSem.Checks.ProcessCreation

section K6a

/-! ## K6a — `check_exit`, `exit_witness`, the two arms -/

/-- An `exit` input: `a7 = 93`, the code in `a0`, a second register `a1`
the arm must NOT read, and nonzero junk in `a2`..`a5` so that an arm
reading any register but `a0` halts with something a pin can see; no
memory.  The number is a numeral, which is how
`tools/check_lean_pin_evidence.py` reads a pin's syscall off its input. -/
def exit_in (code a1 : word) : SyscallInput :=
  SyscallInput.mkInput 93 [code, a1, 11, 13, 17, 19] (fun _ => none) (fun _ => none)

/-- An `exit_group` input: `a7 = 94`, otherwise as `exit_in`. -/
def exit_group_in (code a1 : word) : SyscallInput :=
  SyscallInput.mkInput 94 [code, a1, 11, 13, 17, 19] (fun _ => none) (fun _ => none)

/-! ### The acceptor: one triple in, one triple out -/

/-- `exit(256)` is accepted with the halt recorded as 0: the kernel keeps
`error_code & 0xff` and 256 has an empty low byte.  The return is the 0
the tester synthesizes for a call that never returns.
kernel: kernel/exit.c:exit,do_exit@v6.18.46 -/
theorem check_exit_256_halts_with_zero (m : Model) :
    check_exit (Z_to_bv 64 256) (mkEffect (Z_to_bv 64 0) [] []) m
      = CheckOk (with_halted (Z_to_bv 64 0) m) [] :=
  (check_ret_only_ok_iff _ _ _ _ _ _).mpr
    ⟨rfl, congrArg (fun c => with_halted c m)
      (by decide : (Z_to_bv 64 0 : word) = bv_and (Z_to_bv 64 256) (Z_to_bv 64 255)), rfl⟩

/-- …and the model with the UNMASKED 256 recorded is not what the checker
hands back: the seven high bytes are gone before any status exists.
kernel: kernel/exit.c:exit,do_exit@v6.18.46 -/
theorem check_exit_256_does_not_record_256 (m : Model) :
    check_exit (Z_to_bv 64 256) (mkEffect (Z_to_bv 64 0) [] []) m
      ≠ CheckOk (with_halted (Z_to_bv 64 256) m) [] := by
  intro h
  obtain ⟨_, hm, _⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
  exact absurd (Option.some.inj (congrArg m_halted hm)) (by decide)

/-- `exit(-1)`: the byte of an all-ones register is 255, the classic
`exit(-1)` a shell reports as 255.
kernel: kernel/exit.c:exit,do_exit@v6.18.46 -/
theorem check_exit_minus_one_halts_with_255 (m : Model) :
    check_exit (Z_to_bv 64 (-1)) (mkEffect (Z_to_bv 64 0) [] []) m
      = CheckOk (with_halted (Z_to_bv 64 255) m) [] :=
  (check_ret_only_ok_iff _ _ _ _ _ _).mpr
    ⟨rfl, congrArg (fun c => with_halted c m)
      (by decide : (Z_to_bv 64 255 : word) = bv_and (Z_to_bv 64 (-1)) (Z_to_bv 64 255)), rfl⟩

/-- `exit(0x100000001ff)`: a code with a bit beyond `int` halts with 255.
`SYSCALL_DEFINE1(exit, int, error_code)` narrows the register to `int`
before the mask, and the checker masks the whole register; the two agree
because the low byte of the narrowed word is the low byte of the whole
one — the pin the acceptance would fail if the checker refused or
mis-masked a code above 2^32, which no pin at 256 or -1 can see.  The
probe's `exit wide` case is this call, recorded as run 003.
kernel: kernel/exit.c:exit,do_exit; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem check_exit_wide_halts_with_255 (m : Model) :
    check_exit (Z_to_bv 64 0x100000001ff) (mkEffect (Z_to_bv 64 0) [] []) m
      = CheckOk (with_halted (Z_to_bv 64 255) m) [] :=
  (check_ret_only_ok_iff _ _ _ _ _ _).mpr
    ⟨rfl, congrArg (fun c => with_halted c m)
      (by decide : (Z_to_bv 64 255 : word)
        = bv_and (Z_to_bv 64 0x100000001ff) (Z_to_bv 64 255)), rfl⟩

/-- …and the same code does not halt with `0x1ff`, the `int` the kernel
sees before the mask: the seven high bytes are gone, not one.
kernel: kernel/exit.c:exit,do_exit; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem check_exit_wide_does_not_record_0x1ff (m : Model) :
    check_exit (Z_to_bv 64 0x100000001ff) (mkEffect (Z_to_bv 64 0) [] []) m
      ≠ CheckOk (with_halted (Z_to_bv 64 0x1ff) m) [] := by
  intro h
  obtain ⟨_, hm, _⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
  exact absurd (Option.some.inj (congrArg m_halted hm)) (by decide)

/-- A nonzero return is refused.  `do_exit` never returns, so the only
return the checker can be shown is the tester's synthesized 0, and a
`--mutate` that changes it is the lie this rejects.
kernel: kernel/exit.c:exit,do_exit@v6.18.46 -/
theorem check_exit_rejects_a_nonzero_return (m : Model) :
    check_exit (Z_to_bv 64 256) (mkEffect (Z_to_bv 64 1) [] []) m = CheckReject := rfl

/-- An errno return is refused for the same reason: `exit` has no error
path, so `-EINVAL` on the way out is a lie about a call that cannot fail.
kernel: kernel/exit.c:exit,do_exit@v6.18.46 -/
theorem check_exit_rejects_an_errno (m : Model) :
    check_exit (Z_to_bv 64 256) (mkEffect (Z_to_bv 64 (-22)) [] []) m = CheckReject := rfl

/-- A write is refused.  The two stores the exit path can make through
a pointer the task registered — the owner-died bit `handle_futex_death`
sets in each word of the robust list that the dying task itself holds,
and `mm_release`'s `put_user(0, tsk->clear_child_tid)` behind
`mm_users > 1` — and the three it can make into a ring a declined
syscall would have mapped are listed on the checker, with why none fires
in a run the model admits; so an effect carrying a write is one no exit
of the pinned kernel produces there.  The harness cannot show this
checker a real write (the effect is synthesized), so this pin and the
five ledger pins after it refuse `--mutate` lies alone.
kernel: kernel/fork.c:exit_mm_release,mm_release; kernel/futex/core.c:futex_exit_release,futex_cleanup,exit_robust_list,handle_futex_death@v6.18.46 -/
theorem check_exit_rejects_a_write (m : Model) :
    check_exit (Z_to_bv 64 256) (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 4096, [0])] []) m
      = CheckReject := rfl

/-- A zero-fill is refused.  The zeros ledger records fresh anonymous
memory a call hands out (rw `mmap`/`brk` grants), and exit grants none.
The one zero the exit path can STORE, `mm_release`'s `put_user(0,
tsk->clear_child_tid)`, is a write, and `check_exit_rejects_a_write`
says why it does not fire.
kernel: kernel/exit.c:exit,do_exit; kernel/fork.c:mm_release@v6.18.46 -/
theorem check_exit_rejects_a_zero_fill (m : Model) :
    check_exit (Z_to_bv 64 256) (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 4096, Z_to_bv 64 8)]) m
      = CheckReject := rfl

/-- An unmap is refused.  The first of three pins over the ledgers
`mkEffect` fixes to `[]` — unmaps, copies, copy-ins — stated over
`SyscallEffect.mkEffectU` so that each ledger is offered a lie of its
own: a checker matching only the return, the writes and the zeros passes
every pin above and fails these three.  The lie is `smuggle-unmap`;
`exit_mm` releases the whole mm after the trap and the run does not
continue, so no range is unmapped for anything to observe.
kernel: kernel/exit.c:exit_mm@v6.18.46 -/
theorem check_exit_rejects_an_unmap (m : Model) :
    check_exit (Z_to_bv 64 256)
      (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 4096, Z_to_bv 64 4096)] [] []) m
      = CheckReject := rfl

/-- A copy is refused: nothing on the exit path moves user memory.  The
lie is `smuggle-copy`.
kernel: kernel/exit.c:exit,do_exit@v6.18.46 -/
theorem check_exit_rejects_a_copy (m : Model) :
    check_exit (Z_to_bv 64 256)
      (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] []
        [MemCopy.mkCopy (Z_to_bv 64 4096) (Z_to_bv 64 8192) (Z_to_bv 64 8)] []) m
      = CheckReject := rfl

/-- A copy-in is refused: `exit` and `exit_group` take one `int` and no
pointer, so nothing is read from user memory on the way in.  The lie is
`smuggle-copyin`; like the other five it reaches this arm, since the
terminal effect `testing/syscall-check/main.ml` synthesizes for 93 and 94
passes through the same `mutate` as every other effect.
kernel: kernel/exit.c:exit,exit_group@v6.18.46 -/
theorem check_exit_rejects_a_copyin (m : Model) :
    check_exit (Z_to_bv 64 256)
      (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [] [] [(Z_to_bv 64 4096, 8)]) m
      = CheckReject := rfl

/-- The checker never declines: `exit` takes any `int` and has no gate,
so every code is answered and none is `unmodeled`.
kernel: kernel/exit.c:exit,exit_group@v6.18.46 -/
theorem check_exit_never_declines (code : word) (eff : SyscallEffect) (m : Model) :
    check_exit code eff m ≠ CheckUnmodeled :=
  check_ret_only_no_unmodeled _ _ _ _

/-! ### The witness -/

/-- The witness at 256 is the accepted triple written out, halt 0.
kernel: kernel/exit.c:exit,do_exit@v6.18.46 -/
theorem exit_witness_256_halts_with_zero (m : Model) :
    exit_witness (Z_to_bv 64 256) m
      = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (Z_to_bv 64 0) m) [] :=
  congrArg (fun c => Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted c m) [])
    (by decide : bv_and (Z_to_bv 64 256) (Z_to_bv 64 255) = Z_to_bv 64 0)

/-- The checker accepts its own witness at every code and model: the
receptive field and the complete field meet on the same triple, which is
what makes the arm's `ca_receptive` a statement about `check_exit` and
not only about the spec.
model: `exit_witness` fed to `check_exit`, no spec named -/
theorem check_exit_accepts_its_witness (code : word) (m : Model) (e : SyscallEffect)
    (m' : Model) (evs : List event)
    (h : exit_witness code m = Ok e m' evs) : check_exit code e m = CheckOk m' evs := by
  unfold exit_witness ret_outcome at h
  injection h with he hm hevs
  subst he hm hevs
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- …and the witness is not `Unmodeled` at any code or model.
model: `exit_witness`'s shape, an `Ok` at every argument -/
theorem exit_witness_is_never_unmodeled (code : word) (m : Model) :
    exit_witness code m ≠ Unmodeled := fun h => nomatch h

/-! ### The arms: what `arm_unfold` opens them to -/

/-- The arm reads the code from `a0`: `SYSCALL_DEFINE1(exit, int,
error_code)` has one argument, and on riscv the trap handler saves `a0`
as `orig_a0` before clobbering `a0` with `-ENOSYS` (`do_trap_ecall_u`),
then the wrapper hands the one argument `regs->orig_a0`
(`SC_RISCV_REGS_TO_ARGS`), so a 7 in `a0` beside a 9 in `a1` halts with 7.
`kernel/exit.c` alone cannot say which register that is.
kernel: arch/riscv/kernel/traps.c:do_trap_ecall_u; arch/riscv/include/asm/syscall.h:syscall_handler; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/exit.c:exit@v6.18.46 -/
theorem arm_exit_reads_a0 (m : Model) :
    arm_exit.ca_check (exit_in (Z_to_bv 64 7) (Z_to_bv 64 9)) (mkEffect (Z_to_bv 64 0) [] []) m
      = CheckOk (with_halted (Z_to_bv 64 7) m) [] := by
  simp only [arm_unfold]
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr
    ⟨rfl, congrArg (fun c => with_halted c m)
      (by decide : (Z_to_bv 64 7 : word)
        = bv_and (in_arg (exit_in (Z_to_bv 64 7) (Z_to_bv 64 9)) 0) (Z_to_bv 64 255)), rfl⟩

/-- …and not from `a1`: the same call does not halt with 9.  `a1` is the
SECOND argument the wrapper would pass, and `exit` takes one.
kernel: arch/riscv/kernel/traps.c:do_trap_ecall_u; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/exit.c:exit@v6.18.46 -/
theorem arm_exit_does_not_read_a1 (m : Model) :
    arm_exit.ca_check (exit_in (Z_to_bv 64 7) (Z_to_bv 64 9)) (mkEffect (Z_to_bv 64 0) [] []) m
      ≠ CheckOk (with_halted (Z_to_bv 64 9) m) [] := by
  simp only [arm_unfold]
  intro h
  obtain ⟨_, hm, _⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
  exact absurd (Option.some.inj (congrArg m_halted hm)) (by decide)

/-- `exit_group(0x1245)` through its own arm, with a 9 in `a1`, halts
with `0x45`: the same mask, `(error_code & 0xff) << 8`, on the way into
`do_group_exit`, applied to the one argument the wrapper passes.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/exit.c:exit_group,do_group_exit@v6.18.46 -/
theorem arm_exit_group_halts_with_the_low_byte (m : Model) :
    arm_exit_group.ca_check (exit_group_in (Z_to_bv 64 0x1245) (Z_to_bv 64 9))
        (mkEffect (Z_to_bv 64 0) [] []) m
      = CheckOk (with_halted (Z_to_bv 64 0x45) m) [] := by
  simp only [arm_unfold]
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr
    ⟨rfl, congrArg (fun c => with_halted c m)
      (by decide : (Z_to_bv 64 0x45 : word)
        = bv_and (in_arg (exit_group_in (Z_to_bv 64 0x1245) (Z_to_bv 64 9)) 0)
            (Z_to_bv 64 255)), rfl⟩

/-- …and not with the 9 from `a1`: `SYSCALL_DEFINE1(exit_group, int,
error_code)` has one argument too, and the wrapper hands it `regs->orig_a0`.
kernel: arch/riscv/kernel/traps.c:do_trap_ecall_u; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/exit.c:exit_group@v6.18.46 -/
theorem arm_exit_group_does_not_read_a1 (m : Model) :
    arm_exit_group.ca_check (exit_group_in (Z_to_bv 64 0x1245) (Z_to_bv 64 9))
        (mkEffect (Z_to_bv 64 0) [] []) m
      ≠ CheckOk (with_halted (Z_to_bv 64 9) m) [] := by
  simp only [arm_unfold]
  intro h
  obtain ⟨_, hm, _⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
  exact absurd (Option.some.inj (congrArg m_halted hm)) (by decide)

/-- `exit_group(0x100000001ff)` through its own arm halts with 255: the
probe's `group wide` case, recorded as run 008, and the one arm-level
pin whose code has a bit above `int`.
kernel: kernel/exit.c:exit_group,do_group_exit; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem arm_exit_group_wide_halts_with_255 (m : Model) :
    arm_exit_group.ca_check (exit_group_in (Z_to_bv 64 0x100000001ff) (Z_to_bv 64 9))
        (mkEffect (Z_to_bv 64 0) [] []) m
      = CheckOk (with_halted (Z_to_bv 64 255) m) [] := by
  simp only [arm_unfold]
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr
    ⟨rfl, congrArg (fun c => with_halted c m)
      (by decide : (Z_to_bv 64 255 : word)
        = bv_and (in_arg (exit_group_in (Z_to_bv 64 0x100000001ff) (Z_to_bv 64 9)) 0)
            (Z_to_bv 64 255)), rfl⟩

/-- …and refuses a nonzero return exactly as the `exit` arm does: one
checker, two numbers.
kernel: kernel/exit.c:exit_group,do_group_exit@v6.18.46 -/
theorem arm_exit_group_rejects_a_nonzero_return (m : Model) :
    arm_exit_group.ca_check (exit_group_in (Z_to_bv 64 0x1245) (Z_to_bv 64 9))
        (mkEffect (Z_to_bv 64 1) [] []) m
      = CheckReject := by
  simp only [arm_unfold]
  rfl

/-- The arm's witness is what the arm's checker accepts, through both
`arm_unfold` rewrites: the `ca_witness` field and the `ca_check` field
of `arm_exit` name the same triple.
model: `arm_exit`'s `ca_witness` fed to its `ca_check`, no spec named -/
theorem arm_exit_accepts_its_witness (i : SyscallInput) (m : Model) (e : SyscallEffect)
    (m' : Model) (evs : List event)
    (h : arm_exit.ca_witness i m = Ok e m' evs) : arm_exit.ca_check i e m = CheckOk m' evs := by
  simp only [arm_unfold] at h ⊢
  exact check_exit_accepts_its_witness _ m e m' evs h

/-- The arm's checker never declines, at any input, effect or model:
`exit` has no gate.  The STATEMENT is forced by the record —
`no_declining_checker_over_exit` in `Checks/Cases/Checks/Sys/Dispatch.lean`
proves it of any arm over `exit`'s spec through `ca_sound_unmodeled`, and
`no_lazy_checker_over_exit` the weaker `¬ ∀` through `ca_complete_ok` —
so fed `arm_exit` either would test only the arm's number.  What this
pin adds is the PROOF, which reads `check_exit`'s body through
`check_exit_never_declines` and not the record's fields, so a checker
stubbed to `CheckUnmodeled` fails here and not only in
`Checks/Sys/Table.lean`.
kernel: kernel/exit.c:exit@v6.18.46 -/
theorem arm_exit_never_declines (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_exit.ca_check i eff m ≠ CheckUnmodeled := by
  simp only [arm_unfold]
  exact check_exit_never_declines _ _ _

/-- …and neither does `arm_exit_group`'s, by the same route.
kernel: kernel/exit.c:exit_group@v6.18.46 -/
theorem arm_exit_group_never_declines (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_exit_group.ca_check i eff m ≠ CheckUnmodeled := by
  simp only [arm_unfold]
  exact check_exit_never_declines _ _ _

/-! ### The arms' specs: what `sa_spec` opens to -/

/-- `arm_exit`'s spec field IS `exit_spec` at `a0`: through
`sa_spec_arm_exit` the arm's `ca_arm` admits exactly the halt-with-7 for
a 7 in `a0`, so an arm built over the wrong argument or the wrong spec —
which the record's proof fields could still be supplied for, if its
checker were changed to match — is caught on the spec side too.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/exit.c:exit@v6.18.46 -/
theorem arm_exit_spec_is_exit_at_a0 (m : Model) (o : outcome SyscallEffect) :
    arm_exit.ca_arm.sa_spec (exit_in (Z_to_bv 64 7) (Z_to_bv 64 9)) m o
      ↔ o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (Z_to_bv 64 7) m) [] := by
  simp only [arm_unfold]
  sys_norm

/-- …and `arm_exit_group`'s is `exit_spec` at `a0` as well: the same
input shape under 94 admits the halt-with-7 and not the halt-with-9.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/exit.c:exit_group@v6.18.46 -/
theorem arm_exit_group_spec_is_exit_at_a0 (m : Model) (o : outcome SyscallEffect) :
    arm_exit_group.ca_arm.sa_spec (exit_group_in (Z_to_bv 64 7) (Z_to_bv 64 9)) m o
      ↔ o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (Z_to_bv 64 7) m) [] := by
  simp only [arm_unfold]
  sys_norm

/-- Negative: the spec `arm_exit_group` carries does not allow the halt
with `a1`'s 9.
kernel: arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; kernel/exit.c:exit_group@v6.18.46 -/
theorem arm_exit_group_spec_does_not_read_a1 (m : Model) :
    ¬ arm_exit_group.ca_arm.sa_spec (exit_group_in (Z_to_bv 64 7) (Z_to_bv 64 9)) m
        (Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (Z_to_bv 64 9) m) []) := by
  simp only [arm_unfold]
  sys_refute

/-! ### The table: 93 and 94, in that order -/

/-- The table finds `exit` at 93 and hands back the trusted arm.
kernel: include/uapi/asm-generic/unistd.h:__NR_exit@v6.18.46 -/
theorem checked_table_finds_exit : lookup_ca checked_table 93 = some arm_exit :=
  lookup_ca_checked_table_exit

/-- The table finds `exit_group` at 94 and hands back the trusted arm.
kernel: include/uapi/asm-generic/unistd.h:__NR_exit_group@v6.18.46 -/
theorem checked_table_finds_exit_group : lookup_ca checked_table 94 = some arm_exit_group :=
  lookup_ca_checked_table_exit_group

/-- The two numbers sit in the table in spec order, 93 before 94.  Stated
as a FILTER of the table's numbers rather than as the whole list, so that
the pin says what the ticket owes — these two, in this order — and
survives the next arm's block: the acceptance literal `[93, 94]` is the
whole table only until the next registration.  The guard's refusals —
arms transposed, an arm twice — are `Checks/Cases/Checks/Sys/Table.lean`'s
over fixtures, and `numbers_follow` reads only `ca_no`, so restating them
over the real arms would add nothing to `ca_no_arm_exit_group = 94`.
kernel: include/uapi/asm-generic/unistd.h:__NR_exit,__NR_exit_group@v6.18.46 -/
theorem checked_table_carries_93_then_94 :
    (checked_table.map ca_no).filter (fun n => n == 93 || n == 94) = [93, 94] := by decide

/-! ### The dispatcher instances, over the real table

`check_syscall` and `syscall_spec_witness` dispatch over `checked_table`
itself.  `Checks/Cases/Checks/ExecutableSpecs.lean` and
`Checks/Cases/Checks/Progress.lean` drive them over fixture tables and,
over the real one, at numbers no table carries; the positive at 93 and 94
is this registration's to state, and these pins are where the real table
first answers a call. -/

/-- `check_syscall` at `exit(256)` over the tree's own table: the lookup
finds `arm_exit`, and the answer is `check_exit`'s.  This is the positive
`Checks/Cases/Checks/ExecutableSpecs.lean` could state only over a fixture
while the table was empty.
kernel: kernel/exit.c:exit,do_exit@v6.18.46 -/
theorem check_syscall_accepts_exit_over_the_real_table (m : Model) :
    check_syscall (exit_in (Z_to_bv 64 256) (Z_to_bv 64 9)) (mkEffect (Z_to_bv 64 0) [] []) m
      = CheckOk (with_halted (Z_to_bv 64 0) m) [] := rfl

/-- …and refuses a nonzero return there: the arm the real table hands the
dispatcher is not one that accepts everything.
kernel: kernel/exit.c:exit,do_exit@v6.18.46 -/
theorem check_syscall_rejects_a_return_at_exit_over_the_real_table (m : Model) :
    check_syscall (exit_in (Z_to_bv 64 256) (Z_to_bv 64 9)) (mkEffect (Z_to_bv 64 1) [] []) m
      = CheckReject := rfl

/-- `check_syscall` at `exit_group(0x1245)` over the tree's own table halts
with `0x45`: the lookup finds `arm_exit_group`, not `arm_exit`, and the
mask is the same.
kernel: kernel/exit.c:exit_group,do_group_exit@v6.18.46 -/
theorem check_syscall_accepts_exit_group_over_the_real_table (m : Model) :
    check_syscall (exit_group_in (Z_to_bv 64 0x1245) (Z_to_bv 64 9))
        (mkEffect (Z_to_bv 64 0) [] []) m
      = CheckOk (with_halted (Z_to_bv 64 0x45) m) [] := rfl

/-- The tree's witness at `exit` is not the decline: the side of
`Checks/Cases/Checks/Progress.lean`'s
`the_trees_witness_at_exit_is_the_decline_iff_the_table_lacks_the_arm`
that `checked_table` reaches now that it holds the arm.  Its positive
form: the witness is `exit_witness`'s triple.
kernel: kernel/exit.c:exit,do_exit@v6.18.46 -/
theorem the_trees_witness_at_exit_is_not_the_decline (m : Model) :
    syscall_spec_witness (exit_in (Z_to_bv 64 256) (Z_to_bv 64 9)) m
      = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (Z_to_bv 64 0) m) [] := rfl

/-- …and at `exit_group` too.
kernel: kernel/exit.c:exit_group,do_group_exit@v6.18.46 -/
theorem the_trees_witness_at_exit_group_is_not_the_decline (m : Model) :
    syscall_spec_witness (exit_group_in (Z_to_bv 64 0x1245) (Z_to_bv 64 9)) m
      ≠ Unmodeled := fun h => nomatch h

/-! ### The premises the empty write ledger rests on

Four numbers the checker's docstring names as having no arm, each stated
in the L3 shape `tools/check_decline_registers.py` reads, so that the day
one of them gains an arm the register tool reports the collision, the
`rfl` stops closing, and the write ledger's argument is the first thing
to revisit.  The generated `Checks/Cases/SyscallTable.lean` cannot carry
them: it emits one line per arm of the Rocq table, and none of these is
one. -/

/-- `set_robust_list` (99): the robust list `exit_robust_list` walks is
installed by 99 alone, so no run the model admits reaches the exit with a
list for `handle_futex_death` to store into.
kernel: kernel/futex/syscalls.c:set_robust_list@v6.18.46 -/
theorem set_robust_list_has_no_arm : lookup_arm spec_table 99 = none := rfl

/-- `io_setup` (0): the AIO ring `exit_aio` completes events into is
created by 0 alone.
kernel: fs/aio.c:io_setup@v6.18.46 -/
theorem io_setup_has_no_arm : lookup_arm spec_table 0 = none := rfl

/-- `perf_event_open` (241): the ring `perf_event_exit_task` writes the
`PERF_RECORD_EXIT` record into is opened by 241 alone.
kernel: kernel/events/core.c:perf_event_open@v6.18.46 -/
theorem perf_event_open_has_no_arm : lookup_arm spec_table 241 = none := rfl

/-- `io_uring_setup` (425): the completion ring `io_uring_files_cancel`
posts into is created by 425 alone.
kernel: io_uring/io_uring.c:io_uring_setup@v6.18.46 -/
theorem io_uring_setup_has_no_arm : lookup_arm spec_table 425 = none := rfl

end K6a

-- lean-port sentinel: ticket C-Kernel-Exit appends below this line

/-! ## The wait4 half

Pins over `check_wait4` and `wait4_witness`, C-Kernel-Exit's half of the
checker's file.  Rocq keeps no worked-cases file for this checker
either: its pins on it are stated over the dispatcher, in
`Checks/Examples.v` (`wait4_with_a_child_is_unmodeled`,
`wait4_with_a_child_admits_no_answer`) and `Checks/ProcessCreation.v`
(`wait4_not_unmodeled`, `wait4_answers_only_echild`), and the register
for `Checks/Examples.v` belongs to `Checks/Examples.lean`, where that
file's `exit_dispatch_*` twins already live — so this file carries no
worked-cases register (the coverage header `check_lean_cases_parity.py`
reads), which that tool would refuse in a file that mirrors none.
`wait4_with_a_child_admits_no_answer` below is that
Rocq lemma's twin all the same, proved through the arm.
`wait4_with_a_child_is_unmodeled`, `wait4_checker_echild` and
`wait4_checker_rejects_a_reap` below twin the Rocq `check_syscall`
claims through the registered `arm_wait4`.  Their proofs use the
generated lookup lemma before reusing the checker pins, so the decline
is the arm's and not the dispatcher's missing-number fallback.
The `syscall_spec` readings `wait4_echild` and `wait4_rejects_a_reap`
remain in `Checks/ProcessCreation.lean`.  Every kernel line below was read
at Linux v6.18.46 (commit 1f99e9ab748f).

WHAT IS UNDER TEST is the acceptor, not the spec.  `Checks/Cases/Kernel/Exit.lean`
reads `wait4_spec` off its monad primitives and says which outcomes it
allows; this half offers `check_wait4` the effects a trace could carry —
the one answer, then each lie a kernel cannot tell on this shape — and
requires `CheckOk`, `CheckReject` or `CheckUnmodeled` by name.  The two
files say the same thing about Linux from the two sides of
`check_wait4_sound_ok` and `check_wait4_complete_ok`; what those proofs
cannot catch is both sides moving together — a checker that declined
everywhere beside a spec that admitted nothing would satisfy all four —
and such a checker fails every `CheckOk` and `CheckReject` pin here,
which is why the pins are owed.

Where the harness has the same case for the Rocq acceptor
(`testing/syscall-check/tests/wait4_spec.c`: `--mutate wait4:ret=0`,
`ret=4321`, the errno lies, the `smuggle-*` ledgers and the `fail-closed`
shapes), the kernel line is still the evidence each pin cites: the
probe's verdict is about the extracted Rocq checker, and this file is
about the Lean one.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE. -/

/-! ## The numbers these checks spell out

`4294967295` is a0 after `Syscall.pid32`: the `int` -1, `WAIT_ANY32`,
which `Checks/Cases/Kernel/Exit.lean` pins at its numeral beside
`WNOHANG = 1` and `ECHILD = 10`.  The other options words are
include/uapi/linux/wait.h's bits (Linux v6.18.46) OR'd onto `WNOHANG`:
`3` adds `WUNTRACED`, `5` `WEXITED`, `9` `WCONTINUED`, `16777217`
`WNOWAIT`, `536870913` `__WNOTHREAD`, `1073741825` `__WALL`,
`2147483649` `__WCLONE`; `Sys/Uapi/Sched.lean`'s register says, beside
`WNOHANG`, why it names none of those bits, so they stay numerals here
and each decline pin cites the function that reads its bit.  `0`
for `rusage` is the NULL pointer.  What the model can decide, it
decides: -/

/-- `errno_ret ECHILD` written out: the `long` -10, all 32 high bits set.
kernel: include/uapi/asm-generic/errno-base.h:ECHILD@v6.18.46 -/
example : errno_ret ECHILD = 18446744073709551606 := by decide
/-- ...and its low 32 bits zero-extended: the `int` -10 a checker
comparing 32 bits would take for the same answer.
kernel: include/uapi/asm-generic/errno-base.h:ECHILD@v6.18.46 -/
example : abi_low32 (errno_ret ECHILD) = 4294967286 := by decide
/-- `demo_model` records no child; `with_children` of it records one.
model: the two fixtures' own children field; no kernel behaviour is claimed -/
example : m_has_children demo_model = false ∧ m_has_children (with_children demo_model) = true :=
  ⟨rfl, rfl⟩

section TheAnswer

/-! ## The one answer

`__do_wait` (kernel/exit.c:1665-1710, Linux v6.18.46) seeds
`wo->notask_error = -ECHILD`; with `wo_type = PIDTYPE_MAX` the early exit
is not taken, `do_wait_thread` and `ptrace_do_wait` walk two empty lists
per caller thread (:1689-1700) and return 0, and `notask:` returns the
seed.  `kernel_wait4`
(kernel/exit.c:1848-1889, Linux v6.18.46) reaches its `put_user` only
under `ret > 0`. -/

/-- -ECHILD with the model kept, nothing written, no event: accepted, for
ANY `stat_addr` and any input.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_childless_echild_ok (i : SyscallInput) (stat_addr : word) :
    check_wait4 i 4294967295 stat_addr 1 0 (mkEffect (errno_ret ECHILD) [] []) demo_model
      = CheckOk demo_model [] := rfl

/-- ...and for every model the children gate lets through, read through
the completeness theorem from the spec's own pin.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_childless_echild_ok_for_every_model (i : SyscallInput) (stat_addr : word)
    (m : Model) (hm : m_has_children m = false) :
    check_wait4 i 4294967295 stat_addr 1 0 (mkEffect (errno_ret ECHILD) [] []) m
      = CheckOk m [] :=
  check_wait4_complete_ok i 4294967295 stat_addr 1 0 (mkEffect (errno_ret ECHILD) [] []) m m []
    ((wait4_childless_is_echild_for_every_model stat_addr i m hm _).mpr rfl)

/-- A `stat_addr` at the top of the 64-bit space — all ones, far past
`TASK_SIZE` — is accepted like a NULL one: the pointer is dead at -ECHILD.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
example (i : SyscallInput) :
    check_wait4 i 4294967295 (Z_to_bv 64 (-1)) 1 0 (mkEffect (errno_ret ECHILD) [] []) demo_model
      = CheckOk demo_model [] := rfl

/-- The arm sees a0 and a2 AFTER the row's `pid32`/`waitopts32`
(`Sys/Registry/Kernel/Exit.lean`'s row applies both before `wait4_spec`,
as Rocq's `check_syscall_wait4` does before `check_wait4`).  So the
probe's `trunc` case — a0 = 0x1ffffffff and a2 = 0x100000001, whose low
halves are the `int` -1 and `WNOHANG` — is the modeled shape by the time
it reaches this checker, and the kernel, which reads both as `int`,
answers -ECHILD.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_truncated_args_echild_ok (i : SyscallInput) (stat_addr : word) :
    check_wait4 i (pid32 8589934591) stat_addr (waitopts32 4294967297) 0
        (mkEffect (errno_ret ECHILD) [] []) demo_model = CheckOk demo_model [] := rfl

/-- a0 = -1 sign-extended to 64 bits, the way a C caller passes `pid_t`
-1, and a2 with its whole high half set: both are still `int` -1 and
`WNOHANG` after the row's truncation.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_sign_extended_minus_one_echild_ok (i : SyscallInput) :
    check_wait4 i (pid32 (Z_to_bv 64 (-1))) 0 (waitopts32 18446744069414584321) 0
        (mkEffect (errno_ret ECHILD) [] []) demo_model = CheckOk demo_model [] := rfl

/-- The accepted return, written out: `kernel_wait4` returns a `long`,
so a0 carries -10 in all 64 bits.
kernel: kernel/exit.c:kernel_wait4,__do_wait; include/uapi/asm-generic/errno-base.h:ECHILD@v6.18.46 -/
theorem check_wait4_childless_echild_numeral_ok (i : SyscallInput) :
    check_wait4 i 4294967295 0 1 0 (mkEffect 18446744073709551606 [] []) demo_model
      = CheckOk demo_model [] := rfl

/-- The modeled shape never declines, whatever the effect: the four
gates are all the checker's `CheckUnmodeled`, and `__do_wait` gives this
shape one answer, so a decline here would be a coverage hole the
kernel's own answer does not have.
kernel: kernel/exit.c:__do_wait@v6.18.46 -/
theorem check_wait4_childless_never_unmodeled (i : SyscallInput) (stat_addr : word)
    (eff : SyscallEffect) :
    check_wait4 i 4294967295 stat_addr 1 0 eff demo_model ≠ CheckUnmodeled := by
  unfold check_wait4
  have h0 : ¬ bv_unsigned (4294967295 : word) ≠ WAIT_ANY32 := fun hc => hc (by decide)
  have h1 : ¬ bv_unsigned (1 : word) ≠ WNOHANG := fun hc => hc (by decide)
  have h2 : ¬ (!w_is0 (0 : word)) = true := by decide
  have h3 : ¬ m_has_children demo_model = true := by decide
  rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
  intro h
  split at h
  · split at h <;> simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h

end TheAnswer

section TheLies

/-! ## The lies a kernel cannot tell on this shape

Each is a return or a ledger `__do_wait`'s empty walk cannot produce, and
each is REJECTED — not declined: a trace carrying it is a wrong trace,
not a call outside the model. -/

/-- WNOHANG's bare 0 is what a CLEARED `notask_error` returns
(kernel/exit.c:1704-1709, Linux v6.18.46), and only `wait_consider_task`
on a child or tracee that exists clears it (:1479, :1533, :1539).
kernel: kernel/exit.c:__do_wait@v6.18.46 -/
theorem check_wait4_childless_bare_zero_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 0 1 0 (mkEffect 0 [] []) demo_model = CheckReject := rfl

/-- A pid is a report: for a child the caller does not trace, only
`wait_task_zombie` (kernel/exit.c:1175, Linux v6.18.46) returns one on
`WNOHANG`; a ptraced one is also reported by `wait_task_stopped`, which
sees ptrace-stopped tasks regardless of `WUNTRACED` (:1339-1343).
Neither is reached over empty lists.
kernel: kernel/exit.c:wait_task_zombie,wait_task_stopped,do_wait_thread@v6.18.46 -/
theorem check_wait4_childless_reap_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 0 1 0 (mkEffect 4321 [] []) demo_model = CheckReject := rfl

/-- ...and a reap that also reports a status word through `stat_addr`.
kernel: kernel/exit.c:wait_task_zombie,kernel_wait4@v6.18.46 -/
theorem check_wait4_childless_reap_with_status_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 4096 1 0 (mkEffect 4321 [(4096, [0, 0, 0, 0])] []) demo_model
      = CheckReject := rfl

/-- EVERY return but -ECHILD is rejected, not only the ones sampled: the
return test is equality with `errno_ret ECHILD`.
kernel: kernel/exit.c:__do_wait@v6.18.46 -/
theorem check_wait4_childless_other_return_rejected (i : SyscallInput) (stat_addr r : word)
    (hr : r ≠ errno_ret ECHILD) :
    check_wait4 i 4294967295 stat_addr 1 0 (mkEffect r [] []) demo_model = CheckReject := by
  unfold check_wait4
  split
  · rename_i hc
    exact absurd (by decide) hc
  split
  · rename_i hc
    exact absurd (by decide) hc
  split
  · rename_i hc
    exact absurd hc (by decide)
  split
  · rename_i hc
    exact absurd hc (by decide)
  show (if bv_eqb r (errno_ret ECHILD) = true then CheckOk demo_model [] else CheckReject)
      = CheckReject
  rw [ite_eq_right]
  intro hb
  exact hr ((bv_eqb_eq _ _).mp hb)

/-- -EFAULT (include/uapi/asm-generic/errno-base.h, Linux v6.18.46) is
`kernel_wait4`'s answer to a failed `put_user`, and the `put_user` is
guarded on `ret > 0` (kernel/exit.c:1885-1886, Linux v6.18.46): never
reached at -ECHILD.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem check_wait4_childless_efault_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 0 1 0 (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckReject := rfl

/-- ...not even for a `stat_addr` at the top of the 64-bit space.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem check_wait4_childless_efault_overstat_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 (Z_to_bv 64 (-1)) 1 0 (mkEffect (errno_ret EFAULT) [] []) demo_model
      = CheckReject := rfl

/-- -EINTR needs -ERESTARTSYS — it is `arch_do_signal_or_restart`'s
rewrite of that return when the handler lacks `SA_RESTART`
(arch/riscv/kernel/signal.c:437-443, Linux v6.18.46) — and `do_wait`'s
loop (kernel/exit.c:1722-1730) reaches `signal_pending` and `schedule`
only on that return, which `__do_wait` gives only when `notask_error`
was cleared and `WNOHANG` is off (:1704-1707).
kernel: kernel/exit.c:do_wait,__do_wait; arch/riscv/kernel/signal.c:arch_do_signal_or_restart; include/uapi/asm-generic/errno-base.h:EINTR@v6.18.46 -/
theorem check_wait4_childless_eintr_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 0 1 0 (mkEffect (errno_ret EINTR) [] []) demo_model
      = CheckReject := rfl

/-- -ERESTARTSYS (512, include/linux/errno.h, Linux v6.18.46) is what
`__do_wait` returns to `do_wait`'s loop (kernel/exit.c:1704-1707 and
:1725), never to userspace — `arch_do_signal_or_restart` restarts the
call or rewrites it to -EINTR (arch/riscv/kernel/signal.c:416-424,
:437-443) — and never at all for the `PIDTYPE_MAX` walk over empty
lists.
kernel: kernel/exit.c:__do_wait,do_wait; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem check_wait4_childless_erestartsys_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 0 1 0 (mkEffect (errno_ret 512) [] []) demo_model
      = CheckReject := rfl

/-- -EINVAL belongs to an options word with a bit outside the mask
(kernel/exit.c:1856-1858, Linux v6.18.46), which `WNOHANG` alone is not.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem check_wait4_childless_einval_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 0 1 0 (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckReject := rfl

/-- -ESRCH belongs to `upid == INT_MIN` (kernel/exit.c:1860-1862, Linux
v6.18.46), which -1 is not.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem check_wait4_childless_esrch_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 0 1 0 (mkEffect (errno_ret ESRCH) [] []) demo_model
      = CheckReject := rfl

/-- A status written through `stat_addr` is the copy-out the `ret > 0`
guard skips (kernel/exit.c:1885-1886, Linux v6.18.46): -ECHILD writes
nothing.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_childless_status_write_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 4096 1 0 (mkEffect (errno_ret ECHILD) [(4096, [0, 0, 0, 0])] [])
        demo_model
      = CheckReject := rfl

/-- ...and it zero-fills nothing.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_childless_zeros_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 4096 1 0
        (SyscallEffect.mkEffectU (errno_ret ECHILD) [] [(4096, 4)] [] [] []) demo_model
      = CheckReject := rfl

/-- ...unmaps nothing.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_childless_unmap_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 4096 1 0
        (SyscallEffect.mkEffectU (errno_ret ECHILD) [] [] [(4096, 4096)] [] []) demo_model
      = CheckReject := rfl

/-- ...and a zero-length zero-fill entry is still an entry: the match is
on the ledger's shape, as `check_wait4_childless_empty_write_entry_rejected`
pins for the writes ledger.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_childless_empty_zeros_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 4096 1 0
        (SyscallEffect.mkEffectU (errno_ret ECHILD) [] [(4096, 0)] [] [] []) demo_model
      = CheckReject := rfl

/-- ...as is a zero-length unmap entry.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_childless_empty_unmap_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 4096 1 0
        (SyscallEffect.mkEffectU (errno_ret ECHILD) [] [] [(4096, 0)] [] []) demo_model
      = CheckReject := rfl

/-- ...copies nothing.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_childless_copy_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 4096 1 0
        (SyscallEffect.mkEffectU (errno_ret ECHILD) [] [] [] [MemCopy.mkCopy 4096 4104 4] [])
        demo_model
      = CheckReject := rfl

/-- ...and copies IN nothing: `kernel_wait4` (kernel/exit.c:1848-1889,
Linux v6.18.46) has no `copy_from_user` and no `get_user`, so the fifth
ledger is empty too.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_childless_copyin_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 4096 1 0
        (SyscallEffect.mkEffectU (errno_ret ECHILD) [] [] [] [] [(4096, 4)]) demo_model
      = CheckReject := rfl

/-- 0x00000000_fffffff6, the `int` -10 zero-extended, is the positive
pid 4294967286, not -ECHILD: `kernel_wait4` returns a `long` and the
checker compares all 64 bits of a0.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem check_wait4_childless_zero_extended_echild_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 0 1 0 (mkEffect 4294967286 [] []) demo_model = CheckReject := rfl

/-- No `put_user` runs at -ECHILD (`kernel_wait4` guards it on
`ret > 0`, kernel/exit.c:1885-1886, Linux v6.18.46), so no write entry
of ANY length: an entry carrying zero bytes is as much a lie as one
carrying four.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_childless_empty_write_entry_rejected (i : SyscallInput) :
    check_wait4 i 4294967295 4096 1 0 (mkEffect (errno_ret ECHILD) [(4096, [])] []) demo_model
      = CheckReject := rfl

end TheLies

section TheGates

/-! ## The four gates decline, whatever the trace says

Each gate is a call a real kernel answers with state this model does not
carry (the spec's docstring has the argument, gate by gate); the checker
declines it before any effect is looked at, so the kernel's report is
neither accepted nor rejected.  What the pins fix is that the gates come
before the effect — the order among the four is unobservable, each
answering the same `CheckUnmodeled` — so a decline is `CheckUnmodeled`
for EVERY effect, including the reap the kernel really produced. -/

/-- EVERY `upid` but -1 declines: the gate is the whole complement of
`WAIT_ANY32`, spelled as its value 4294967295 here so that the statement
names no constant of the model's.  `kernel_wait4` answers `INT_MIN`
-ESRCH before any lookup (kernel/exit.c:1860-1862, Linux v6.18.46) and
maps every other value to a `wo_type < PIDTYPE_MAX` (:1866-1875); for
those `__do_wait` answers -ECHILD at its early exit only when the number
names no `struct pid`, or one with no task of the selected type
(:1676-1678) — `upid = 0` selects the caller's own process group
(:1869-1871) — and otherwise from `do_wait_pid`
(:1682-1685) or the walk over the caller's threads (:1686-1700), which
is state this model does not carry.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_other_upid_unmodeled (i : SyscallInput) (upid stat_addr options rusage : word)
    (h : bv_unsigned upid ≠ 4294967295) (eff : SyscallEffect) (m : Model) :
    check_wait4 i upid stat_addr options rusage eff m = CheckUnmodeled := by
  have h' : bv_unsigned upid ≠ WAIT_ANY32 := by
    rw [show WAIT_ANY32 = 4294967295 from by decide]
    exact h
  unfold check_wait4
  rw [ite_eq_left h']

/-- `upid = 0` selects the caller's process group (kernel/exit.c:1869-1871,
Linux v6.18.46): declined, for any effect.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem check_wait4_pgrp_self_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 0 0 1 0 eff m = CheckUnmodeled := rfl

/-- A positive `upid` names one child (kernel/exit.c:1872-1875, Linux
v6.18.46): declined, for any effect.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem check_wait4_child_pid_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 4321 0 1 0 eff m = CheckUnmodeled := rfl

/-- `INT_MIN` as `pid32` reads it: -ESRCH before the selector
(kernel/exit.c:1860-1862, Linux v6.18.46), and declined here rather than
answered.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem check_wait4_int_min_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 2147483648 0 1 0 eff m = CheckUnmodeled := rfl

/-- `INT_MAX`, the top of the positive range: `kernel_wait4` selects it as
one child (kernel/exit.c:1872-1875, Linux v6.18.46), so it is declined
like every positive pid; with `INT_MIN`, -1 and 0 above this completes
the `int` edges.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem check_wait4_int_max_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 2147483647 0 1 0 eff m = CheckUnmodeled := rfl

/-- EVERY options word but `WNOHANG` declines; the gate is spelled as
the value 1 (include/uapi/linux/wait.h, Linux v6.18.46) so that, as
with `upid`, the statement names no constant of the model's.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_other_options_unmodeled (i : SyscallInput) (stat_addr options rusage : word)
    (h : bv_unsigned options ≠ 1) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 4294967295 stat_addr options rusage eff m = CheckUnmodeled := by
  have h' : bv_unsigned options ≠ WNOHANG := by
    rw [show WNOHANG = 1 from by decide]
    exact h
  unfold check_wait4
  have h0 : ¬ bv_unsigned (4294967295 : word) ≠ WAIT_ANY32 := fun hc => hc (by decide)
  rw [ite_eq_right h0, ite_eq_left h']

/-- Without `WNOHANG` the call may sleep once a child exists (`__do_wait`,
kernel/exit.c:1704-1707, Linux v6.18.46): `do_wait`'s loop (:1722-1730)
leaves with -ERESTARTSYS on a pending signal, which
`arch_do_signal_or_restart` (arch/riscv/kernel/signal.c:437-443) hands
userspace as -EINTR when the handler lacks `SA_RESTART`; the childless
caller gets the -ECHILD seed without sleeping, but the word is declined
for every model and any effect.
kernel: kernel/exit.c:do_wait,__do_wait; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem check_wait4_blocking_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 4294967295 0 0 0 eff m = CheckUnmodeled := rfl

/-- `WNOHANG|WUNTRACED` asks about a child's stop (`wait_task_stopped`,
kernel/exit.c:1331, Linux v6.18.46): declined.
kernel: kernel/exit.c:wait_task_stopped@v6.18.46 -/
theorem check_wait4_wuntraced_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 4294967295 0 3 0 eff m = CheckUnmodeled := rfl

/-- EVERY non-NULL `rusage` declines: `SYSCALL_DEFINE4(wait4, ...)`
(kernel/exit.c:1907-1918, Linux v6.18.46) copies it out only under
`err > 0`, so answering would be sound, and the decline is the spec's
declared narrowing.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem check_wait4_rusage_unmodeled (i : SyscallInput) (stat_addr rusage : word)
    (h : w_is0 rusage = false) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 4294967295 stat_addr 1 rusage eff m = CheckUnmodeled := by
  unfold check_wait4
  have h0 : ¬ bv_unsigned (4294967295 : word) ≠ WAIT_ANY32 := fun hc => hc (by decide)
  have h1 : ¬ bv_unsigned (1 : word) ≠ WNOHANG := fun hc => hc (by decide)
  have h' : (!w_is0 rusage) = true := by
    rw [h]
    rfl
  rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h']

/-- ...on one concrete non-NULL pointer, the page boundary 4096.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem check_wait4_rusage_page_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 4294967295 0 1 4096 eff m = CheckUnmodeled := rfl

/-- A caller the model gave a child is declined on EVERY argument shape
and for EVERY effect: this is `Checks/Examples.v`'s
`wait4_with_a_child_is_unmodeled` on the arm rather than through
`check_syscall`.  With a child, `__do_wait`'s walk (kernel/exit.c:1686-1700,
Linux v6.18.46) reaches `wait_consider_task`, which clears `notask_error`
at :1479, :1533 and :1539, so the answer depends on state the model does
not carry.
kernel: kernel/exit.c:__do_wait,wait_consider_task,do_wait_thread,wait_task_zombie@v6.18.46 -/
theorem check_wait4_with_a_child_is_unmodeled (i : SyscallInput)
    (upid stat_addr options rusage : word) (eff : SyscallEffect) (m : Model)
    (hc : m_has_children m = true) :
    check_wait4 i upid stat_addr options rusage eff m = CheckUnmodeled := by
  unfold check_wait4
  by_cases h1 : bv_unsigned upid ≠ WAIT_ANY32
  · rw [ite_eq_left h1]
  rw [ite_eq_right h1]
  by_cases h2 : bv_unsigned options ≠ WNOHANG
  · rw [ite_eq_left h2]
  rw [ite_eq_right h2]
  by_cases h3 : (!w_is0 rusage) = true
  · rw [ite_eq_left h3]
  rw [ite_eq_right h3, ite_eq_left hc]

/-- ...and on the fixture that records one, the reap the kernel really
produced is neither accepted nor rejected.
kernel: kernel/exit.c:__do_wait,wait_task_zombie@v6.18.46 -/
theorem check_wait4_with_a_child_reap_unmodeled (i : SyscallInput) :
    check_wait4 i 4294967295 0 1 0 (mkEffect 4321 [] []) (with_children demo_model)
      = CheckUnmodeled := rfl

/-- ...nor is -ECHILD, the answer the spec would have given without the gate.
kernel: kernel/exit.c:__do_wait,do_wait_thread@v6.18.46 -/
theorem check_wait4_with_a_child_echild_unmodeled (i : SyscallInput) :
    check_wait4 i 4294967295 0 1 0 (mkEffect (errno_ret ECHILD) [] []) (with_children demo_model)
      = CheckUnmodeled := rfl

/-- The gates come first: a decline is a decline even when the trace
carries the reap the kernel produced — `wait4_spec.c`'s
`--mutate wait4:ret=4321 -- blocking`, on the Lean acceptor.
kernel: kernel/exit.c:kernel_wait4,do_wait@v6.18.46 -/
theorem check_wait4_blocking_reap_unmodeled (i : SyscallInput) :
    check_wait4 i 4294967295 0 0 0 (mkEffect 4321 [] []) demo_model = CheckUnmodeled := rfl

/-- The arm's contract is the POST-truncation word.  a0 = -1
sign-extended, as the raw register carries it, is not `WAIT_ANY32` and
declines here: a row that forgot `pid32` would decline `wait4(-1, …)`
itself, which is what `check_wait4_sign_extended_minus_one_echild_ok`
above rules out for the row that applies it.
model: the arm's contract is the post-`pid32` word `Sys/Registry/Kernel/Exit.lean`'s row hands it, and `CheckedArm.ca_complete_ok` beside `Table.arms_agree` is what forbids a row without `pid32` (the spec row answers where an untruncated checker declines); what Linux makes of the raw register is `check_wait4_sign_extended_minus_one_echild_ok`'s claim, not this pin's -/
theorem check_wait4_raw_sign_extended_minus_one_unmodeled (i : SyscallInput)
    (eff : SyscallEffect) (m : Model) :
    check_wait4 i (Z_to_bv 64 (-1)) 0 1 0 eff m = CheckUnmodeled := rfl

/-- `WNOHANG|WEXITED` (the probe's `badopt` case): `WEXITED` is outside
`kernel_wait4`'s mask (kernel/exit.c:1856-1858, Linux v6.18.46) and
Linux answers -EINVAL.  The spec declines the word rather than
answering it, so the checker neither accepts nor rejects the kernel's
own -EINVAL here.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem check_wait4_badopt_einval_unmodeled (i : SyscallInput) (m : Model) :
    check_wait4 i 4294967295 0 5 0 (mkEffect (errno_ret EINVAL) [] []) m = CheckUnmodeled := rfl

/-- `WNOHANG|WNOWAIT` (0x01000001; `WNOWAIT` is 0x01000000 in
include/uapi/linux/wait.h, Linux v6.18.46): `waitid`'s bit, outside the
same mask, -EINVAL from Linux and a decline here.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem check_wait4_wnowait_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 4294967295 0 16777217 0 eff m = CheckUnmodeled := rfl

/-- `WNOHANG|__WCLONE`: inside the mask, and `eligible_child`
(kernel/exit.c:1142-1167, Linux v6.18.46) then waits on the children
whose `exit_signal` is not `SIGCHLD` — a set this model does not carry.
A checker testing "has the `WNOHANG` bit" instead of equality would
accept it.
kernel: kernel/exit.c:eligible_child,kernel_wait4@v6.18.46 -/
theorem check_wait4_wclone_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 4294967295 0 2147483649 0 eff m = CheckUnmodeled := rfl

/-- `WNOHANG|__WALL`: `eligible_child` returns 1 for every child, clone
or not.
kernel: kernel/exit.c:eligible_child@v6.18.46 -/
theorem check_wait4_wall_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 4294967295 0 1073741825 0 eff m = CheckUnmodeled := rfl

/-- `WNOHANG|__WNOTHREAD`: `__do_wait` stops its thread walk after
`current` (kernel/exit.c:1698-1699, Linux v6.18.46).
kernel: kernel/exit.c:__do_wait@v6.18.46 -/
theorem check_wait4_wnothread_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 4294967295 0 536870913 0 eff m = CheckUnmodeled := rfl

/-- `WNOHANG|WCONTINUED`: a continued child becomes reportable through
`wait_task_continued` (kernel/exit.c:1403-1410, Linux v6.18.46).
kernel: kernel/exit.c:wait_task_continued@v6.18.46 -/
theorem check_wait4_wcontinued_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 4294967295 0 9 0 eff m = CheckUnmodeled := rfl

/-- `upid = INT_MIN` with the -ESRCH Linux really gives it
(kernel/exit.c:1860-1862, Linux v6.18.46): declined, not accepted.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem check_wait4_int_min_esrch_unmodeled (i : SyscallInput) (m : Model) :
    check_wait4 i 2147483648 0 1 0 (mkEffect (errno_ret ESRCH) [] []) m = CheckUnmodeled := rfl

/-- A named pid with the -ECHILD Linux gives a childless caller
(`__do_wait`'s `notask_error` seed): declined, not accepted — the
answer is right, the shape is not the modeled one.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem check_wait4_child_pid_echild_unmodeled (i : SyscallInput) :
    check_wait4 i 4321 0 1 0 (mkEffect (errno_ret ECHILD) [] []) demo_model = CheckUnmodeled := rfl

/-- `upid = -1234` as `pid32` delivers it (4294966062): process group
1234, `kernel_wait4`'s `upid < 0` arm (kernel/exit.c:1866-1868, Linux
v6.18.46), the probe's `pgrpother` case.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem check_wait4_pgrp_other_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 4294966062 0 1 0 eff m = CheckUnmodeled := rfl

/-- a3 = 0x100000000 is a non-NULL `struct rusage __user *`: the
pointer is 64 bits wide, so a checker narrowing it to 32 would accept
this as NULL.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem check_wait4_rusage_high_bits_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_wait4 i 4294967295 0 1 4294967296 eff m = CheckUnmodeled := rfl

end TheGates

section TheWitness

/-! ## The witness: the outcome the progress argument hands the dispatcher

`wait4_witness` (`Checks/Sys/Kernel/Exit.lean`, Rocq's
`Checks/Witness/Kernel/Exit.v`) is the answer the model is shown to allow
for every input and model; `Checks/Progress.lean` consumes it through
the arm the V ticket registers.  These pins read it on the shapes the
checker is pinned on above, and tie the two together: what the witness
answers, the checker accepts, and where the witness declines, so does
the checker. -/

/-- On the modeled shape the witness is -ECHILD with the model kept and no
event: the effect `check_wait4_childless_echild_ok` accepts.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_witness_childless_is_echild (i : SyscallInput) (stat_addr : word) :
    wait4_witness 4294967295 stat_addr 1 0 i demo_model
      = Ok (mkEffect (errno_ret ECHILD) [] []) demo_model [] := rfl

/-- ...and for every model the children gate lets through, read through
`wait4_witness_ok` and the spec's own pin: the spec admits the witness,
and on this shape it admits exactly one outcome, so the witness is it.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_witness_childless_is_echild_for_every_model (i : SyscallInput) (stat_addr : word)
    (m : Model) (hm : m_has_children m = false) :
    wait4_witness 4294967295 stat_addr 1 0 i m = Ok (mkEffect (errno_ret ECHILD) [] []) m [] :=
  (wait4_childless_is_echild_for_every_model stat_addr i m hm _).mp
    (wait4_witness_ok 4294967295 stat_addr 1 0 i m)

/-- A pid other than -1 is the first gate: `Unmodeled`, as the checker
declines it in `TheGates` — `kernel_wait4` would select that pid
(kernel/exit.c:1872-1875, Linux v6.18.46) and answer for a child the
model does not have.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem wait4_witness_declines_a_pid (i : SyscallInput) (m : Model) :
    wait4_witness 1 0 1 0 i m = Unmodeled := rfl

/-- An option word other than WNOHANG alone is the second gate: without
`WNOHANG`, `do_wait` (kernel/exit.c:1722-1730, Linux v6.18.46) may sleep
once a child exists.
kernel: kernel/exit.c:do_wait@v6.18.46 -/
theorem wait4_witness_declines_other_options (i : SyscallInput) (m : Model) :
    wait4_witness 4294967295 0 0 0 i m = Unmodeled := rfl

/-- A non-NULL rusage is the third gate: `SYSCALL_DEFINE4(wait4, ...)`
(kernel/exit.c:1907-1918, Linux v6.18.46) would copy it out under
`err > 0`, a write the model declines to describe.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem wait4_witness_declines_rusage (i : SyscallInput) (m : Model) :
    wait4_witness 4294967295 0 1 8 i m = Unmodeled := rfl

/-- EVERY `upid` but -1 declines at the witness, the twin of
`check_wait4_other_upid_unmodeled`: the gate reads the whole word, so a
witness reading its low 32 bits, or testing anything but equality,
fails this for some word.  `kernel_wait4` maps every other value to a
selector (kernel/exit.c:1860-1875, Linux v6.18.46) whose answer is
state this model does not carry.
kernel: kernel/exit.c:kernel_wait4@v6.18.46 -/
theorem wait4_witness_other_upid_unmodeled (i : SyscallInput) (upid stat_addr options rusage : word)
    (h : bv_unsigned upid ≠ 4294967295) (m : Model) :
    wait4_witness upid stat_addr options rusage i m = Unmodeled := by
  have h' : bv_unsigned upid ≠ WAIT_ANY32 := by
    rw [show WAIT_ANY32 = 4294967295 from by decide]
    exact h
  unfold wait4_witness
  rw [ite_eq_left h']

/-- EVERY options word but `WNOHANG` declines at the witness, the twin of
`check_wait4_other_options_unmodeled`; spelled as the value 1 so the
statement names no constant of the model's.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_witness_other_options_unmodeled (i : SyscallInput) (stat_addr options rusage : word)
    (h : bv_unsigned options ≠ 1) (m : Model) :
    wait4_witness 4294967295 stat_addr options rusage i m = Unmodeled := by
  have h' : bv_unsigned options ≠ WNOHANG := by
    rw [show WNOHANG = 1 from by decide]
    exact h
  unfold wait4_witness
  have h0 : ¬ bv_unsigned (4294967295 : word) ≠ WAIT_ANY32 := fun hc => hc (by decide)
  rw [ite_eq_right h0, ite_eq_left h']

/-- EVERY non-NULL `rusage` declines at the witness, the twin of
`check_wait4_rusage_unmodeled`: the gate is `w_is0` on all 64 bits, so
a witness testing the low word alone fails this at 0x100000000.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem wait4_witness_other_rusage_unmodeled (i : SyscallInput) (stat_addr rusage : word)
    (h : w_is0 rusage = false) (m : Model) :
    wait4_witness 4294967295 stat_addr 1 rusage i m = Unmodeled := by
  unfold wait4_witness
  have h0 : ¬ bv_unsigned (4294967295 : word) ≠ WAIT_ANY32 := fun hc => hc (by decide)
  have h1 : ¬ bv_unsigned (1 : word) ≠ WNOHANG := fun hc => hc (by decide)
  have h' : (!w_is0 rusage) = true := by
    rw [h]
    rfl
  rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h']

/-- A model with a child is the fourth gate, on the modeled arguments: the
twin of `wait4_with_a_child_is_unmodeled`'s reading, for the witness —
with a child, `__do_wait`'s walk reaches `wait_consider_task` and the
answer depends on the child's state.
kernel: kernel/exit.c:__do_wait,wait_consider_task,do_wait_thread,wait_task_zombie@v6.18.46 -/
theorem wait4_witness_with_a_child_is_unmodeled (i : SyscallInput) (stat_addr : word) (m : Model)
    (hm : m_has_children m = true) :
    wait4_witness 4294967295 stat_addr 1 0 i m = Unmodeled := by
  unfold wait4_witness
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left hm]

/-- The witness's `upid` gate reads the whole word, as the checker's does
(`check_wait4_raw_sign_extended_minus_one_unmodeled`): a0 = -1
sign-extended, the raw register, is not `WAIT_ANY32` and declines; the
row's `pid32` is what makes `wait4(-1, …)` the modeled call.
model: the arm's contract is the post-`pid32` word the row hands it, and `CheckedArm.ca_receptive` over the row's spec is what a registration without `pid32` would fail; what Linux makes of the raw register is `wait4_witness_childless_is_echild`'s claim, not this pin's -/
theorem wait4_witness_raw_sign_extended_minus_one_unmodeled (i : SyscallInput) (m : Model) :
    wait4_witness (Z_to_bv 64 (-1)) 0 1 0 i m = Unmodeled := rfl

/-- ...and its `rusage` gate reads 64 bits, as
`check_wait4_rusage_high_bits_unmodeled` pins for the checker: a3 =
0x100000000 is a non-NULL `struct rusage __user *` and declines.
kernel: kernel/exit.c:wait4@v6.18.46 -/
theorem wait4_witness_rusage_high_bits_unmodeled (i : SyscallInput) (m : Model) :
    wait4_witness 4294967295 0 1 4294967296 i m = Unmodeled := rfl

/-- What the witness answers, the checker accepts, for every argument
and every model: receptiveness meets completeness at the arm.
model: `check_wait4_complete_ok` applied to `wait4_witness_ok`; no kernel behaviour is claimed -/
theorem check_wait4_accepts_the_witness (i : SyscallInput) (upid stat_addr options rusage : word)
    (m m' : Model) (eff : SyscallEffect) (evs : List event)
    (h : wait4_witness upid stat_addr options rusage i m = Ok eff m' evs) :
    check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs := by
  have hw := wait4_witness_ok upid stat_addr options rusage i m
  rw [h] at hw
  exact check_wait4_complete_ok i upid stat_addr options rusage eff m m' evs hw

/-- ...and where the witness is `Unmodeled`, the checker declines every
effect: the witness never points at a call the checker would judge.
model: `check_wait4_complete_unmodeled` applied to `wait4_witness_ok`; no kernel behaviour is claimed -/
theorem check_wait4_declines_where_the_witness_does (i : SyscallInput)
    (upid stat_addr options rusage : word) (m : Model) (eff : SyscallEffect)
    (h : wait4_witness upid stat_addr options rusage i m = Unmodeled) :
    check_wait4 i upid stat_addr options rusage eff m = CheckUnmodeled := by
  have hw := wait4_witness_ok upid stat_addr options rusage i m
  rw [h] at hw
  exact check_wait4_complete_unmodeled i upid stat_addr options rusage m eff hw

end TheWitness

section TheDispatcher

/-! ## Through the dispatcher: the twin of `Checks/Examples.v`

`wait4_with_a_child_admits_no_answer` is Rocq's statement that the
children gate is not merely undecided but closed: with a child recorded,
no `Ok` outcome at all reaches syscall 260.  Rocq proves it from
`check_syscall_complete_ok` and `wait4_with_a_child_is_unmodeled`.
The spec-dispatcher proof here reuses `check_wait4_complete_ok`
and `check_wait4_with_a_child_is_unmodeled` — after reading the spec
dispatcher's row for 260 the way `Checks/Examples.lean`'s
`exit_dispatch_iff` reads it for 93. -/

/-- Rocq: `Examples.wait4_with_a_child_admits_no_answer`.
kernel: kernel/exit.c:__do_wait,do_wait_thread,wait_task_zombie@v6.18.46 -/
theorem wait4_with_a_child_admits_no_answer (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) (hno : bv_unsigned i.in_sysno = 260)
    (hc : m_has_children m = true) :
    ¬ syscall_spec i m (Ok eff m' evs) := by
  intro h
  unfold syscall_spec dispatch at h
  rw [hno] at h
  have h' : wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3)
      i m (Ok eff m' evs) := h
  have hk := check_wait4_complete_ok i _ _ _ _ eff m m' evs h'
  rw [check_wait4_with_a_child_is_unmodeled i _ _ _ _ eff m hc] at hk
  simp only [reduceCtorEq] at hk

end TheDispatcher

section TheCheckedDispatcher

/-! ## Through the checked dispatcher

These pins follow the generated lookup to `arm_wait4`, then reuse the
checker pins above.  The concrete model is Rocq's `pc_model`; its
supplementary groups differ from `demo_model`'s, but wait4 never reads
them. -/

/-- Rocq: `Examples.wait4_with_a_child_is_unmodeled`,
`theories/LinuxProcessSem/Checks/Examples.v:457`.
kernel: kernel/exit.c:__do_wait,do_wait_thread,wait_task_zombie@v6.18.46 -/
theorem wait4_with_a_child_is_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (hno : bv_unsigned i.in_sysno = 260) (hc : m_has_children m = true) :
    check_syscall i eff m = CheckUnmodeled := by
  unfold check_syscall check_syscall_in
  rw [hno, lookup_ca_checked_table_wait4]
  simp only [arm_unfold]
  exact check_wait4_with_a_child_is_unmodeled i _ _ _ _ eff m hc

/-- Rocq: `ProcessCreation.wait4_checker_echild`,
`theories/LinuxProcessSem/Checks/ProcessCreation.v:1066`.
kernel: kernel/exit.c:kernel_wait4,__do_wait@v6.18.46 -/
theorem wait4_checker_echild :
    check_syscall wait4_input_any (mkEffect (errno_ret ECHILD) [] []) pc_model
      = CheckOk pc_model [] := by
  unfold check_syscall check_syscall_in
  rw [show bv_unsigned wait4_input_any.in_sysno = 260 from by decide,
    lookup_ca_checked_table_wait4]
  simp only [arm_unfold]
  obtain ⟨h0, h1, h2, h3⟩ := wait4_input_any_args
  rw [h0, h1, h2, h3]
  exact check_wait4_childless_echild_ok_for_every_model wait4_input_any 0 pc_model (by decide)

/-- Rocq: `ProcessCreation.wait4_checker_rejects_a_reap`,
`theories/LinuxProcessSem/Checks/ProcessCreation.v:1071`.
kernel: kernel/exit.c:wait_task_zombie,wait_task_stopped,do_wait_thread@v6.18.46 -/
theorem wait4_checker_rejects_a_reap :
    check_syscall wait4_input_any (mkEffect 4321 [] []) pc_model = CheckReject := by
  unfold check_syscall check_syscall_in
  rw [show bv_unsigned wait4_input_any.in_sysno = 260 from by decide,
    lookup_ca_checked_table_wait4]
  simp only [arm_unfold]
  obtain ⟨h0, h1, h2, h3⟩ := wait4_input_any_args
  rw [h0, h1, h2, h3]
  exact check_wait4_childless_reap_rejected wait4_input_any

end TheCheckedDispatcher

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Kernel.Exit
