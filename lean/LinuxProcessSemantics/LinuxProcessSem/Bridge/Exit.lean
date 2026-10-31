import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics

/-! A bounded common representation for the two exit arms.

The shared file is consumed directly by Lean and Rocq. These theorems relate
each prover's existing syscall specification to its own interpretation of
that file. They do not identify the two model-state types or prove that the
two interpreters agree; `lean/CORRESPONDENCE.md` records that remaining bridge.
-/

namespace LinuxProcessSemantics.LinuxProcessSem.Bridge.Exit

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Exit

/-- Byte literals bound the common syntax, not the production specification
or its raw 64-bit syscall arguments. -/
inductive Clause where
  | halt (argument mask result : byte)
  | decline
  deriving DecidableEq

def serialize : Clause → List byte
  | .halt argument mask result => [0#8, argument, mask, result]
  | .decline => [1#8]

def deserialize : List byte → Option Clause
  | [tag, argument, mask, result] =>
      if tag = 0#8 then some (.halt argument mask result) else none
  | [tag] => if tag = 1#8 then some .decline else none
  | _ => none

theorem deserialize_serialize (c : Clause) : deserialize (serialize c) = some c := by
  cases c <;> simp [serialize, deserialize]

theorem serialize_injective : Function.Injective serialize := by
  intro a b h
  have := congrArg deserialize h
  simpa only [deserialize_serialize, Option.some.injEq] using this

def denote : Clause → Sys SyscallEffect
  | .halt argument mask result => fun i =>
      (set_halted (bv_and (in_arg i argument.toNat) (Z_to_bv 64 (bv_unsigned mask))) ;;
        ret_only (Z_to_bv 64 (bv_unsigned result))) i
  | .decline => unmodeled

/-- A complete outcome, including the full post-model and every effect ledger.
It uses each development's actual `with_halted`, whose extra state fields are
part of the remaining cross-prover obligation. -/
def evaluate (c : Clause) (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match c with
  | .halt argument mask result =>
      Ok (mkEffect (Z_to_bv 64 (bv_unsigned result)) [] [])
        (with_halted (bv_and (in_arg i argument.toNat) (Z_to_bv 64 (bv_unsigned mask))) m) []
  | .decline => Unmodeled

theorem denote_normal_form (c : Clause) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : denote c i m o ↔ o = evaluate c i m := by
  cases c with
  | decline => rfl
  | halt argument mask result =>
    cases o with
    | Unmodeled => simp [denote, evaluate, Monad.bind, set_halted, Monad.modify, ret_only, Monad.pure]
    | Ok eff m' evs =>
      constructor
      · rintro ⟨x, m1, evs1, evs2, h1, h2, hevs⟩
        change Ok x m1 evs1 = Ok () _ [] at h1
        cases h1
        change Ok eff m' evs2 = Ok _ _ [] at h2
        cases h2
        have hevs : evs = [] := by simpa only [List.nil_append] using hevs
        subst evs
        rfl
      · intro h
        cases h
        exact Monad.bind_ok _ _ i m () _ [] _ _ [] rfl rfl

def exit_clause : Clause := .halt 0#8 255#8 0#8

def artifact_text : String :=
  include_str "../../../../theories/LinuxProcessSem/Bridge/exit.hex"

/-- Read all bytes, rejecting odd lengths and trailing tokens. The established
image hex reader remains an explicitly audited leaf on each side. -/
def read_artifact (text : String) : Option Clause :=
  if text.utf8ByteSize % 2 = 0 then
    (hex_read_bytes text 0 (text.utf8ByteSize / 2)).bind deserialize
  else none

def artifact_clause : Option Clause := read_artifact artifact_text

theorem artifact_checked : artifact_clause = some exit_clause := by decide

theorem artifact_unique (c : Clause) (h : artifact_clause = some c) : c = exit_clause := by
  rw [artifact_checked] at h
  exact (Option.some.inj h).symm

theorem exit_spec_denotes (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    exit_spec (in_arg i 0) i m o ↔ denote exit_clause i m o := Iff.rfl

def exit_number (no : word) : Prop := bv_unsigned no = 93 ∨ bv_unsigned no = 94

theorem exit_dispatch_denotes (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hno : exit_number i.in_sysno) : syscall_spec i m o ↔ denote exit_clause i m o := by
  rcases hno with hno | hno
  all_goals
    unfold syscall_spec dispatch
    rw [hno]
    exact exit_spec_denotes i m o

/-- The public statement consumes the checked artifact rather than taking
agreement with the artifact as a hypothesis. -/
theorem exit_dispatch_artifact (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hno : exit_number i.in_sysno) :
    syscall_spec i m o ↔ ∃ c, artifact_clause = some c ∧ denote c i m o := by
  constructor
  · intro h
    exact ⟨exit_clause, artifact_checked, (exit_dispatch_denotes i m o hno).1 h⟩
  · rintro ⟨c, hc, h⟩
    rw [artifact_unique c hc] at h
    exact (exit_dispatch_denotes i m o hno).2 h

theorem exit_dispatch_normal_form (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (hno : exit_number i.in_sysno) : syscall_spec i m o ↔ o = evaluate exit_clause i m :=
  (exit_dispatch_denotes i m o hno).trans (denote_normal_form exit_clause i m o)

/-- Normalize the bitvector primitive to the same unsigned arithmetic formula
used on the Rocq side. This holds for every raw word, not only the pilot code. -/
theorem status_mod256 (code : word) :
    bv_unsigned (bv_and code (Z_to_bv 64 255)) = bv_unsigned code % 256 := by
  change ((code.toNat &&& (2 ^ 8 - 1) : Nat) : Int) = (code.toNat : Int) % 256
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem exit_dispatch_status (i : SyscallInput) (m m' : Model) (eff : SyscallEffect)
    (evs : List event) (hno : exit_number i.in_sysno)
    (h : syscall_spec i m (Ok eff m' evs)) :
    (m_halted m').map bv_unsigned = some (bv_unsigned (in_arg i 0) % 256) := by
  have h := (exit_dispatch_normal_form i m _ hno).1 h
  cases h
  change some (bv_unsigned (bv_and (in_arg i 0) (Z_to_bv 64 255))) = _
  rw [status_mod256]

end LinuxProcessSemantics.LinuxProcessSem.Bridge.Exit
