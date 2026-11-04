(** * LinuxProcessSem.Checks.ProcsParentPid — root children keep their reparent move

    QA, not trusted specification.  A table key is not the root's Linux
    tgid.  Learning that tgid must not consume a child's one reparent move.
    These cases exercise the table writers and the released getppid checker,
    including the next answer after the real parent exits. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics State Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs ProcsChildPids ProcsPrivateFrame ProcsSharedFrame ProcsSyncOnce.
Import ListNotations.
Open Scope bv_scope.

(** The contract output can be compared across a change to the table writers. *)
Goal True. idtac "PARENT_PID_CONTRACTS_BEGIN". exact I. Qed.
Check pstep_single_next.
Check pstep_single_err.
Check pstep_x_at_agree_iff.
Check pstep_x_at_released_iff.
Check pstep_x_at_flat_iff.
Check pstep_at_no_ext_iff.
Check child_pids_ok.
Check child_pids_ok_absorb.
Check child_pids_ok_replace.
Check child_pids_ok_clone.
Check child_pids_ok_reap.
Check pstep_at_preserves_child_pids.
Check child_pids_ok_one_proc.
Check child_pids_reachable.
Check owned_wait4_answers_child.
Goal True. idtac "PARENT_PID_CONTRACTS_END". exact I. Qed.

Goal True. idtac "ROOT_PARENT_CLOSURE_BEGIN". exact I. Qed.
Check pstep_single_next.
Print Assumptions pstep_single_next.
Check pstep_single_err.
Print Assumptions pstep_single_err.
Check pstep_x_at_agree_iff.
Print Assumptions pstep_x_at_agree_iff.
Check pstep_x_at_released_iff.
Print Assumptions pstep_x_at_released_iff.
Check pstep_x_at_flat_iff.
Print Assumptions pstep_x_at_flat_iff.
Check pstep_at_no_ext_iff.
Print Assumptions pstep_at_no_ext_iff.
Check child_pids_ok_absorb.
Print Assumptions child_pids_ok_absorb.
Check pstep_at_preserves_child_pids.
Print Assumptions pstep_at_preserves_child_pids.
Check child_pids_reachable.
Print Assumptions child_pids_reachable.
Check ProcsPrivateFrame.syscall_spec_private_shared.
Print Assumptions ProcsPrivateFrame.syscall_spec_private_shared.
Check ProcsPrivateFrame.pstep_at_private_frame.
Print Assumptions ProcsPrivateFrame.pstep_at_private_frame.
Check ProcsSharedFrame.syscall_spec_shared_frame.
Print Assumptions ProcsSharedFrame.syscall_spec_shared_frame.
Check ProcsSharedFrame.pstep_at_shared_frame.
Print Assumptions ProcsSharedFrame.pstep_at_shared_frame.
Check ProcsSyncOnce.other_step_keeps_entry.
Print Assumptions ProcsSyncOnce.other_step_keeps_entry.
Check ProcsPeerGates.unlink_keeps_peer_names.
Print Assumptions ProcsPeerGates.unlink_keeps_peer_names.
Goal True. idtac "ROOT_PARENT_CLOSURE_END". exact I. Qed.

Definition pp_launch : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

Definition pp_cfg (ms : machine_state) : config := mkCfg ms pp_launch.
Definition pp_root (ms : machine_state) : ProcessEntry := one_entry (pp_cfg ms).
Definition pp_child (ms : machine_state) : ProcessEntry :=
  child_entry (pp_root ms) (pp_cfg ms) (pp_cfg ms) 2.
Definition pp_system (ms : machine_state) : pconfig :=
  mkPCfg [(one_pid, pp_root ms); (2, pp_child ms)] one_pid
    (pcfg_shared (one_proc (pp_cfg ms))).

Definition pp_getppid (p : word) (m : Model) :=
  check_syscall (mkInput 173 [0; 0; 0; 0; 0; 0]
                  (fun _ => None) (fun _ => None))
    (mkEffect p [] []) m.

Definition pp_answer_unspent (p : word) (P : pconfig) : bool :=
  match look P 2 with
  | Some e =>
      match pp_getppid p (pe_model e) with
      | CheckOk m [] => negb (m_reparent_moved m)
      | _ => false
      end
  | None => false
  end.

(** A child cloned before the silent root pin answers the real tgid and
    still has its move.  Seeding it with key 1 and spending the move on
    the first answer fails this case. *)
Example root_child_before_pin_keeps_move : forall ms,
  pp_answer_unspent 37 (pin_root (pp_system ms) (pp_root ms) 37) = true.
Proof. intros ms. check_eq. Qed.

(** After that answer and the root's exit, the child's next getppid can
    answer a different reaper.  orphan_at_exit itself is not changed. *)
Example root_child_after_exit_answers_reaper : forall ms,
  let P := pin_root (pp_system ms) (pp_root ms) 37 in
  match look P 2, look P one_pid with
  | Some child, Some root =>
      match pp_getppid 37 (pe_model child) with
      | CheckOk child_model [] =>
          let P' := absorb P child (mkCfg ms child_model) in
          let P'' := absorb P' root
            (mkCfg ms (with_halted 0 (pe_model root))) in
          match look P'' 2 with
          | Some orphan =>
              pe_parent orphan = None /\
              match pp_getppid 84 (pe_model orphan) with
              | CheckOk _ [] => True
              | _ => False
              end
          | None => False
          end
      | _ => False
      end
  | _, _ => False
  end.
Proof. intros ms. vm_compute. split; [reflexivity | exact I]. Qed.

(** A later child starts with the already-pinned tgid, not key 1. *)
Example root_child_after_pin_keeps_move : forall ms,
  let root := one_entry (mkCfg ms (with_tid 37 pp_launch)) in
  let child := child_entry root (pp_cfg ms) (pp_cfg ms) 2 in
  match pp_getppid 37 (pe_model child) with
  | CheckOk m [] => m_ppid m = 37 /\ m_reparent_moved m = false
  | _ => False
  end.
Proof. intros ms. vm_compute. split; reflexivity. Qed.

(** The root's own first tid call aligns existing children too. *)
Example root_tid_absorption_keeps_child_move : forall ms,
  pp_answer_unspent 37
    (absorb (pp_system ms) (pp_root ms) (mkCfg ms (with_tid 37 pp_launch))) = true.
Proof. intros ms. check_eq. Qed.

(** The extension's absorption has the same first-pin obligation. *)
Example root_tid_extension_absorption_keeps_child_move : forall ms,
  pp_answer_unspent 37
    (absorb_x (pp_system ms) (pp_root ms) (mkCfg ms (with_tid 37 pp_launch))
      init_nsctx empty_nsstate) = true.
Proof. intros ms. check_eq. Qed.
