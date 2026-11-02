(** * LinuxProcessSem.Checks.MemoryMaterialization — lazy backing checks

    These checks pin the access-to-accounting seam used by sparse anonymous
    mappings: page expansion deduplicates repeated touches, recorded syscall
    ranges are included, and a cross-page access either materializes every new
    page or none of them.  Instruction reporting itself is checked separately
    by [Checks.RiscvAccessReporting]. *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State StackLayout.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.
Open Scope bv_scope.

Definition page_numbers (pages : list word) : list Z :=
  List.map bv_unsigned pages.

Definition materialized_numbers (result : option (list word))
    : option (list Z) :=
  match result with
  | Some pages => Some (page_numbers pages)
  | None => None
  end.

Example cross_page_expansion_is_complete :
  page_numbers (access_pages 0xffc 8) = [0x1000%Z; 0%Z].
Proof. vm_compute. reflexivity. Qed.

Example repeated_page_is_charged_once :
  materialized_numbers
    (materialize_accesses [(0, 0x2000)] [] 0 0x2000
       [(0x10, 8%nat); (0x20, 8%nat)]) = Some [0%Z].
Proof. vm_compute. reflexivity. Qed.

Example already_materialized_page_is_not_charged_twice :
  materialized_numbers
    (materialize_accesses [(0, 0x2000)] [0] 0x1000 0x1000
       [(0x10, 8%nat)]) = Some [0%Z].
Proof. vm_compute. reflexivity. Qed.

Example cross_page_access_materializes_both_pages :
  materialized_numbers
    (materialize_accesses [(0, 0x2000)] [] 0 0x2000
       [(0xffc, 8%nat)]) = Some [0x1000%Z; 0%Z].
Proof. vm_compute. reflexivity. Qed.

Example cross_page_access_fails_atomically_at_limit :
  materialized_numbers
    (materialize_accesses [(0, 0x2000)] [] 0 0x1000
       [(0xffc, 8%nat)]) = None.
Proof. vm_compute. reflexivity. Qed.

Example ordinary_mapping_does_not_consume_lazy_budget :
  materialized_numbers
    (materialize_accesses [] [] 0 0 [(0xffc, 8%nat)]) = Some [].
Proof. vm_compute. reflexivity. Qed.

Example syscall_copyout_reports_exact_byte_range :
  syscall_effect_accesses (mkEffect 0 [(0xfff, [0; 0])] [])
  = [(0xfff, 2%nat)].
Proof. vm_compute. reflexivity. Qed.

Example syscall_copyout_cross_page_is_atomic :
  materialized_numbers
    (materialize_accesses [(0, 0x2000)] [] 0 0x2000
      (syscall_effect_accesses (mkEffect 0 [(0xfff, [0; 0])] [])))
  = Some [0x1000%Z; 0%Z].
Proof. vm_compute. reflexivity. Qed.

Example syscall_copyout_cross_page_fails_without_partial_charge :
  materialized_numbers
    (materialize_accesses [(0, 0x2000)] [] 0 0x1000
      (syscall_effect_accesses (mkEffect 0 [(0xfff, [0; 0])] [])))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example demand_zero_grant_does_not_count_as_copyout :
  syscall_effect_accesses (mkEffect 0 [] [(0, 0x100000)]) = [].
Proof. reflexivity. Qed.

Example syscall_copyins_precede_copyouts :
  syscall_effect_accesses
    (mkEffectU 0 [(0x3000, [0; 0])] [] [] [] [(0x1000, 4%nat)])
  = [(0x1000, 4%nat); (0x3000, 2%nat)].
Proof. vm_compute. reflexivity. Qed.

(** The extracted public checker must thread the accounted post-model, not
    the raw syscall-body post-model.  These two writes touch distinct pages
    of one lazy reservation under a one-page backing limit.  The first call
    charges its page; the second sees that charge and takes the atomic
    materialization-fault result. *)
Definition accounted_write_model : Model :=
  with_vm_backing [(0, 0x2000)] []
    (init_model [] 0 0 (Z_to_bv 64 sp_window_lo) (Z_to_bv 64 (sp_window_lo + 4096)) 0x1000
       (mkProcInput [] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
                     net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false Sv48)).

Definition byte_at (wanted : word) : word -> option byte :=
  fun a => if bv_eqb a wanted then Some 0 else None.

Definition write_input_at (a : word) : SyscallInput :=
  mkInput 64 [1; a; 1; 0; 0; 0] (byte_at a) (fun _ => None).

Definition write_effect_at (a : word) : SyscallEffect :=
  mkEffectU 1 [] [] [] [] [(a, 1%nat)].

Definition first_accounted_write : option check_result :=
  check_syscall_for_run (write_input_at 0) (write_effect_at 0)
    accounted_write_model.

Example accounted_checker_threads_first_touch :
  match first_accounted_write with
  | Some (CheckOk m _) => page_numbers (m_vm_materialized m) = [0%Z]
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

Definition second_accounted_write : option check_result :=
  match first_accounted_write with
  | Some (CheckOk m _) =>
      check_syscall_for_run (write_input_at 0x1000)
        (write_effect_at 0x1000) m
  | result => result
  end.

Example accounted_checker_preserves_charge_between_syscalls :
  second_accounted_write = None.
Proof. vm_compute. reflexivity. Qed.
