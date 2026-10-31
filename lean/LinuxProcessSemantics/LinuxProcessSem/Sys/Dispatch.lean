import LinuxProcessSemantics.LinuxProcessSem.Monad

/-! # LinuxProcessSem.Sys.Dispatch — a syscall as a value, and the dispatcher over them

Mirrors `theories/LinuxProcessSem/Sys/Dispatch.v`.

TRUST BOUNDARY: this file is part of the trusted specification.

An arm is a value: its number and what it admits.  The dispatcher is a
lookup in a list, written once; a number with no arm is `unmodeled`, in
one place, fail closed. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad

/-- One modeled syscall: the number it answers to, and the effects it
admits given the raw `SyscallInput`. -/
structure SpecArm where
  mkSpecArm ::
  sa_no   : Int
  sa_spec : Sys SyscallEffect

/-- The first arm answering to `n`, if any. -/
def lookup_arm (t : List SpecArm) (n : Int) : Option SpecArm :=
  match t with
  | [] => none
  | a :: r => if a.sa_no = n then some a else lookup_arm r n

/-- Dispatch: the arm for this input's syscall number, or `unmodeled`. -/
def dispatch (t : List SpecArm) : Sys SyscallEffect :=
  fun i m o =>
    match lookup_arm t (bv_unsigned i.in_sysno) with
    | some a => a.sa_spec i m o
    | none   => unmodeled i m o

/-- The numbers a table covers, in the table's order. -/
def arm_numbers (t : List SpecArm) : List Int := t.map SpecArm.sa_no

theorem dispatch_unmodeled (t : List SpecArm) (i : SyscallInput) (m : Model) :
    lookup_arm t (bv_unsigned i.in_sysno) = none → dispatch t i m Unmodeled := by
  intro h
  unfold dispatch
  rw [h]
  exact unmodeled_intro i m

theorem dispatch_arm (t : List SpecArm) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) (a : SpecArm) :
    lookup_arm t (bv_unsigned i.in_sysno) = some a →
    (dispatch t i m o ↔ a.sa_spec i m o) := by
  intro h
  unfold dispatch
  rw [h]

end LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
