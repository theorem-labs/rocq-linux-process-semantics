import LinuxProcessSemantics.LinuxProcessSem.Bridge.Exit

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.ExitBridge

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Bridge.Exit

def input255 : SyscallInput :=
  SyscallInput.mkInput 93#64 [255#64, 7#64] (fun _ => none) (fun _ => none)

private theorem input255_exit : exit_number input255.in_sysno := Or.inl rfl

theorem correct_answer_accepted (m : Model) :
    syscall_spec input255 m (evaluate exit_clause input255 m) :=
  (exit_dispatch_normal_form _ _ _ input255_exit).2 rfl

theorem group_answer_accepted (m : Model) :
    syscall_spec {input255 with in_sysno := 94#64} m
      (evaluate exit_clause {input255 with in_sysno := 94#64} m) :=
  (exit_dispatch_normal_form _ _ _ (Or.inr rfl)).2 rfl

private def halted (o : outcome SyscallEffect) : Option word :=
  match o with
  | Ok _ m _ => m_halted m
  | Unmodeled => none

private def returned (o : outcome SyscallEffect) : Option word :=
  match o with
  | Ok eff _ _ => some eff.eff_ret
  | Unmodeled => none

def wide_input : SyscallInput :=
  SyscallInput.mkInput 93#64 [0x1ff#64] (fun _ => none) (fun _ => none)

private theorem wide_input_exit : exit_number wide_input.in_sysno := Or.inl rfl

theorem wide_status_accepted (m : Model) :
    syscall_spec wide_input m (Ok (mkEffect 0#64 [] []) (with_halted 255#64 m) []) :=
  (exit_dispatch_normal_form _ _ _ wide_input_exit).2 rfl

theorem unmasked_wide_status_rejected (m : Model) :
    ¬ syscall_spec wide_input m (Ok (mkEffect 0#64 [] []) (with_halted 0x1ff#64 m) []) := by
  intro h
  have h := congrArg halted ((exit_dispatch_normal_form _ _ _ wide_input_exit).1 h)
  change (some 0x1ff#64 : Option word) = some 255#64 at h
  exact (by decide : (some 0x1ff#64 : Option word) ≠ some 255#64) h

theorem wrong_mask_rejected (m : Model) :
    ¬ syscall_spec input255 m (evaluate (.halt 0#8 127#8 0#8) input255 m) := by
  intro h
  have h := congrArg halted ((exit_dispatch_normal_form _ _ _ input255_exit).1 h)
  change (some 127#64 : Option word) = some 255#64 at h
  exact (by decide : (some 127#64 : Option word) ≠ some 255#64) h

theorem wrong_argument_rejected (m : Model) :
    ¬ syscall_spec input255 m (evaluate (.halt 1#8 255#8 0#8) input255 m) := by
  intro h
  have h := congrArg halted ((exit_dispatch_normal_form _ _ _ input255_exit).1 h)
  change (some 7#64 : Option word) = some 255#64 at h
  exact (by decide : (some 7#64 : Option word) ≠ some 255#64) h

theorem wrong_return_rejected (m : Model) :
    ¬ syscall_spec input255 m (evaluate (.halt 0#8 255#8 1#8) input255 m) := by
  intro h
  have h := congrArg returned ((exit_dispatch_normal_form _ _ _ input255_exit).1 h)
  change (some 1#64 : Option word) = some 0#64 at h
  exact (by decide : (some 1#64 : Option word) ≠ some 0#64) h

theorem unmodeled_rejected (m : Model) : ¬ syscall_spec input255 m Unmodeled := by
  intro h
  have h := (exit_dispatch_normal_form _ _ _ input255_exit).1 h
  cases h

theorem decline_unmodeled_accepted (i : SyscallInput) (m : Model) :
    denote .decline i m Unmodeled := rfl

theorem decline_success_rejected (i : SyscallInput) (m : Model) :
    ¬ denote .decline i m (evaluate exit_clause i m) := by
  intro h
  cases h

-- These are syntax tests, not alternative syscall behavior.
theorem wrong_mask_has_different_serialization :
    serialize (.halt 0#8 127#8 0#8) ≠ serialize exit_clause := by decide

theorem decline_decoded : read_artifact "01" = some .decline := by decide
theorem unknown_tag_rejected : read_artifact "02" = none := by decide
theorem wrong_arity_rejected : read_artifact "00" = none := by decide
theorem odd_length_rejected : read_artifact "0000ff0" = none := by decide
theorem trailing_byte_rejected : read_artifact "0000ff0000" = none := by decide
theorem invalid_hex_rejected : read_artifact "0000gg00" = none := by decide

theorem high_status_normalized :
    bv_unsigned (bv_and (Z_to_bv 64 0x1000001ff) (Z_to_bv 64 255)) = 255 := by decide

theorem full_status_rejected :
    bv_unsigned (bv_and (Z_to_bv 64 0x1000001ff) (Z_to_bv 64 255)) ≠ 0x1000001ff := by decide

theorem seven_bit_remainder_rejected :
    bv_unsigned (bv_and (Z_to_bv 64 255) (Z_to_bv 64 255)) ≠
      bv_unsigned (Z_to_bv 64 255) % 128 := by decide

end LinuxProcessSemantics.LinuxProcessSem.Checks.ExitBridge
