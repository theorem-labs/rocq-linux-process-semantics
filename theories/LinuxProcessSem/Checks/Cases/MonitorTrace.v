(** * LinuxProcessSem.Checks.Cases.MonitorTrace — monitor process replay

    This replay starts at the model after [ParentTrace]'s successful clone.
    Each checker state is the [CheckOk] successor of its preceding call.
    The one infinite [ppoll] is instead a step under [Run.waits_end], where
    its ready result has the recorded descriptor events and its model
    successor is the state that starts the following checker call.

    This file does not reconstruct the RISC-V instructions between system
    calls.  In particular, it does not prove a run-relation path from the
    machine successor of call 23 to the separately constructed machine state
    at [ppoll], nor from that [ppoll] machine successor to call 25's input
    registers.  The trace records system calls, not those intervening
    instructions; the replay threads their model states instead. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import ParentTrace.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel Require Import
  Capability Sys.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs Require Import
  EventFd Fcntl Open ReadWrite Readdir Select Signalfd Stat.

(* =========================================================================
   Call words and checker states
   ========================================================================= *)

Definition monitor_trace_check := parent_trace_check.
Definition monitor_trace_next := parent_trace_next.
Definition monitor_trace_call := parent_trace_call.
Definition monitor_trace_minus1 := parent_trace_minus1.

Definition monitor_trace_s00 : Model := parent_trace_s35.

Definition monitor_trace_child_ns : list byte := [51; 50; 48; 47; 110; 115].
Definition monitor_trace_ns_ipc : list byte := [105; 112; 99].
Definition monitor_trace_ns_mnt : list byte := [109; 110; 116].
Definition monitor_trace_ns_net : list byte := [110; 101; 116].
Definition monitor_trace_ns_pid : list byte := [112; 105; 100].
Definition monitor_trace_ns_uts : list byte := [117; 116; 115].

Definition monitor_trace_stat_in (name : list byte) : SyscallInput :=
  mkInput 79 [6; 8192; 0x3000; 0; 0; 0] (proc_path_mem name) ns_buf_wmem.

Definition monitor_trace_ns_stat (name : list byte) (ino : Z) : SyscallInput * SyscallEffect :=
  (monitor_trace_stat_in name,
   with_copyins [(8192, 4%nat)]
     (mkEffect 0 [(0x3000, stat_of ino 0x8124 0 0 0)] [])).

Definition monitor_trace_c01 : SyscallInput * SyscallEffect :=
  (proc_open_in 3 monitor_trace_child_ns 0x208000,
   with_copyins [(8192, 7%nat)] (mkEffect 6 [] [])).
Definition monitor_trace_c02 : SyscallInput * SyscallEffect :=
  monitor_trace_ns_stat monitor_trace_ns_ipc 1.
Definition monitor_trace_c03 : SyscallInput * SyscallEffect :=
  monitor_trace_ns_stat monitor_trace_ns_mnt 2.
Definition monitor_trace_c04 : SyscallInput * SyscallEffect :=
  monitor_trace_ns_stat monitor_trace_ns_net 3.
Definition monitor_trace_c05 : SyscallInput * SyscallEffect :=
  monitor_trace_ns_stat monitor_trace_ns_pid 4.
Definition monitor_trace_c06 : SyscallInput * SyscallEffect :=
  monitor_trace_ns_stat monitor_trace_ns_uts 5.
Definition monitor_trace_c07 : SyscallInput * SyscallEffect :=
  (monitor_trace_call 57 6 0 0 0 0 0, mkEffect 0 [] []).
Definition monitor_trace_c08 : SyscallInput * SyscallEffect :=
  (capset_input (Z_to_le_bytes 24 0),
   mkEffectU 0 [] [] [] [] cap_ledger3).
Definition monitor_trace_c09 : SyscallInput * SyscallEffect :=
  (prctl_in 4 1 0 0 0, mkEffect 0 [] []).
Definition monitor_trace_c10 : SyscallInput * SyscallEffect :=
  (prctl_in 1 9 0 0 0, mkEffect 0 [] []).
Definition monitor_trace_c11 : SyscallInput * SyscallEffect :=
  (efd_write_in 5 8 efd_one,
   with_copyins [(0x10000, 8%nat)] (mkEffect 8 [] [])).
Definition monitor_trace_c12 : SyscallInput * SyscallEffect :=
  (monitor_trace_call 57 5 0 0 0 0 0, mkEffect 0 [] []).
Definition monitor_trace_c13 : SyscallInput * SyscallEffect :=
  (proc_open_in 3 s_self_fd 0x98900,
   with_copyins [(8192, 8%nat)] (mkEffect 5 [] [])).
Definition monitor_trace_c14 : SyscallInput * SyscallEffect :=
  (procfd_fstat_in 5,
   mkEffect 0 [(0x3000, stat_of 6 PROCFD_DIR_MODE 6 0 0)] []).
Definition monitor_trace_c15 : SyscallInput * SyscallEffect :=
  (mkInput 25 [5; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None),
   mkEffect 0x18800 [] []).
Definition monitor_trace_c16 : SyscallInput * SyscallEffect :=
  (monitor_trace_call 222 0 8192 3 0x22 monitor_trace_minus1 0,
   mkEffectU 0x7fff9428b000 [] [(0x7fff9428b000, 8192)] [] [] []).
Definition monitor_trace_c17 : SyscallInput * SyscallEffect :=
  (mkInput 25 [5; 2; 1; 0; 0; 0] (fun _ => None) (fun _ => None),
   mkEffect 0 [] []).

Definition monitor_trace_dirbuf : word := 0x7fff9428b058.
Definition monitor_trace_dir_wmem : word -> option byte :=
  bytes_at monitor_trace_dirbuf (repeat (Z_to_bv 8 0) 2048).
Definition monitor_trace_getdents_in : SyscallInput :=
  mkInput 61 [5; monitor_trace_dirbuf; 2048; 0; 0; 0] (fun _ => None)
    monitor_trace_dir_wmem.
Definition monitor_trace_listing : list (word * list byte) :=
  [ (0x7fff9428b058, drec 1 1 DT_DIR [46]);
    (0x7fff9428b070, drec 2 2 DT_DIR [46; 46]);
    (0x7fff9428b088, drec 3 3 DT_LNK [48]);
    (0x7fff9428b0a0, drec 4 4 DT_LNK [49]);
    (0x7fff9428b0b8, drec 5 5 DT_LNK [50]);
    (0x7fff9428b0d0, drec 6 6 DT_LNK [51]);
    (0x7fff9428b0e8, drec 7 7 DT_LNK [52]);
    (0x7fff9428b100, drec 8 66 DT_LNK [53]) ].
Definition monitor_trace_c18 : SyscallInput * SyscallEffect :=
  (monitor_trace_getdents_in, mkEffect 192 monitor_trace_listing []).
Definition monitor_trace_c19 : SyscallInput * SyscallEffect :=
  (monitor_trace_call 57 3 0 0 0 0 0, mkEffect 0 [] []).
Definition monitor_trace_c20 : SyscallInput * SyscallEffect :=
  (monitor_trace_getdents_in, mkEffect 0 [] []).
Definition monitor_trace_c21 : SyscallInput * SyscallEffect :=
  (monitor_trace_call 57 5 0 0 0 0 0, mkEffect 0 [] []).
Definition monitor_trace_c22 : SyscallInput * SyscallEffect :=
  (monitor_trace_call 215 0x7fff9428b000 8192 0 0 0 0,
   mkEffectU 0 [] [] [(0x7fff9428b000, 8192)] [] []).
Definition monitor_trace_c23 : SyscallInput * SyscallEffect :=
  (sfd_in (-1) 8 0x80800 sfd_sigchld,
   with_copyins [(0x2000, 8%nat)] (mkEffect 3 [] [])).

Definition monitor_trace_s01 : Model := monitor_trace_next monitor_trace_c01 monitor_trace_s00.
Definition monitor_trace_s02 : Model := monitor_trace_next monitor_trace_c02 monitor_trace_s01.
Definition monitor_trace_s03 : Model := monitor_trace_next monitor_trace_c03 monitor_trace_s02.
Definition monitor_trace_s04 : Model := monitor_trace_next monitor_trace_c04 monitor_trace_s03.
Definition monitor_trace_s05 : Model := monitor_trace_next monitor_trace_c05 monitor_trace_s04.
Definition monitor_trace_s06 : Model := monitor_trace_next monitor_trace_c06 monitor_trace_s05.
Definition monitor_trace_s07 : Model := monitor_trace_next monitor_trace_c07 monitor_trace_s06.
Definition monitor_trace_s08 : Model := monitor_trace_next monitor_trace_c08 monitor_trace_s07.
Definition monitor_trace_s09 : Model := monitor_trace_next monitor_trace_c09 monitor_trace_s08.
Definition monitor_trace_s10 : Model := monitor_trace_next monitor_trace_c10 monitor_trace_s09.
Definition monitor_trace_s11 : Model := monitor_trace_next monitor_trace_c11 monitor_trace_s10.
Definition monitor_trace_s12 : Model := monitor_trace_next monitor_trace_c12 monitor_trace_s11.
Definition monitor_trace_s13 : Model := monitor_trace_next monitor_trace_c13 monitor_trace_s12.
Definition monitor_trace_s14 : Model := monitor_trace_next monitor_trace_c14 monitor_trace_s13.
Definition monitor_trace_s15 : Model := monitor_trace_next monitor_trace_c15 monitor_trace_s14.
Definition monitor_trace_s16 : Model := monitor_trace_next monitor_trace_c16 monitor_trace_s15.
Definition monitor_trace_s17 : Model := monitor_trace_next monitor_trace_c17 monitor_trace_s16.
Definition monitor_trace_s18 : Model := monitor_trace_next monitor_trace_c18 monitor_trace_s17.
Definition monitor_trace_s19 : Model := monitor_trace_next monitor_trace_c19 monitor_trace_s18.
Definition monitor_trace_s20 : Model := monitor_trace_next monitor_trace_c20 monitor_trace_s19.
Definition monitor_trace_s21 : Model := monitor_trace_next monitor_trace_c21 monitor_trace_s20.
Definition monitor_trace_s22 : Model := monitor_trace_next monitor_trace_c22 monitor_trace_s21.
Definition monitor_trace_s23 : Model := monitor_trace_next monitor_trace_c23 monitor_trace_s22.

(* =========================================================================
   The infinite ppoll step
   ========================================================================= *)

(** The [ppoll] model begins at the checked successor of call 23 and leaves
    that model unchanged.  The machine state supplies the traced ecall
    arguments and its pollfd bytes.  The trace does not contain the
    intervening RISC-V instructions that would establish those registers and
    bytes from call 23's machine successor. *)

Definition monitor_trace_ppoll_ms : machine_state := pp_wait_bwrap_ms.
Definition monitor_trace_ppoll_i : SyscallInput :=
  sys_input [] monitor_trace_ppoll_ms (Z_to_bv 64 73).
Definition monitor_trace_ppoll_eff : SyscallEffect :=
  with_copyins
    (ppoll_reads monitor_trace_ppoll_i monitor_trace_s23
       (in_arg monitor_trace_ppoll_i 0) (unfds32 (in_arg monitor_trace_ppoll_i 1))
       (in_arg monitor_trace_ppoll_i 2) (in_arg monitor_trace_ppoll_i 3)
       (in_arg monitor_trace_ppoll_i 4))
    (mkEffect (Z_to_bv 64 1)
       (ppoll_writeback (in_arg monitor_trace_ppoll_i 0) [0; 1]%Z) []).
Definition monitor_trace_c24 : SyscallInput * SyscallEffect :=
  (monitor_trace_ppoll_i, monitor_trace_ppoll_eff).
(** The ready [ppoll] only changes its machine state, so its model successor
    is exactly the state used by call 25. *)
Definition monitor_trace_s24 : Model := monitor_trace_s23.

Lemma monitor_trace_ppoll_wakeable :
  ppoll_wakeable_b monitor_trace_ppoll_i monitor_trace_s23 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma monitor_trace_ppoll_plan :
  ppoll_plan monitor_trace_ppoll_i monitor_trace_s23
    (in_arg monitor_trace_ppoll_i 0) (unfds32 (in_arg monitor_trace_ppoll_i 1))
    (in_arg monitor_trace_ppoll_i 2) (in_arg monitor_trace_ppoll_i 3)
    (in_arg monitor_trace_ppoll_i 4)
  = PpPoll PsToNone ([[0; 1]; [0; 1; 9]])%Z.
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_ppoll_steps_under_waits_end : forall cfg,
  sstep_wcfg [] cfg waits_end
    (mkCfg monitor_trace_ppoll_ms monitor_trace_s23) []
    (SNext (mkCfg (advance_past_svc
      (apply_effect monitor_trace_ppoll_ms monitor_trace_ppoll_eff)) monitor_trace_s24)).
Proof.
  intros cfg.
  apply (sstep_wcfg_wake [] cfg waits_end monitor_trace_ppoll_ms monitor_trace_s23
           (Z_to_bv 64 73) monitor_trace_ppoll_eff monitor_trace_s23 monitor_trace_s24 []).
  - vm_compute. reflexivity.
  - reflexivity.
  - split; [reflexivity | exact monitor_trace_ppoll_wakeable].
  - unfold ppoll_wake_spec.
    exists monitor_trace_ppoll_i, monitor_trace_s23, [], [].
    split; [reflexivity |]. split; [| reflexivity].
    exists monitor_trace_s23, monitor_trace_s24, [], [].
    split; [reflexivity |]. split; [| reflexivity].
    cbv beta zeta. rewrite monitor_trace_ppoll_wakeable. cbn [negb].
    rewrite monitor_trace_ppoll_plan. cbv iota.
    exists (Z_to_bv 64 1,
      ppoll_writeback (in_arg monitor_trace_ppoll_i 0) [0; 1]%Z),
      monitor_trace_s23, [], [].
    split; [| split; reflexivity].
    exists (Z_to_bv 64 1,
      ppoll_writeback (in_arg monitor_trace_ppoll_i 0) [0; 1]%Z).
    split; [| reflexivity].
    exists [0; 1]%Z. split; [vm_compute; reflexivity |].
    split; [intros Hc; vm_compute in Hc; discriminate Hc | vm_compute; reflexivity].
  - apply spurious_refusal_family_on. apply injected_family_off_ppoll. reflexivity.
  - vm_compute. reflexivity.
  - apply materialize_model_accesses_no_lazy. reflexivity.
Qed.

Example monitor_trace_ppoll_is_error_under_waits_may_hang : forall cfg,
  sstep_wcfg [] cfg waits_may_hang
    (mkCfg monitor_trace_ppoll_ms monitor_trace_s23) [] SError.
Proof.
  intros cfg.
  apply (sstep_wcfg_syscall_unmodeled [] cfg waits_may_hang
           monitor_trace_ppoll_ms monitor_trace_s23 (Z_to_bv 64 73)).
  - vm_compute. reflexivity.
  - reflexivity.
  - apply (check_syscall_sound_unmodeled _ (mkEffect 0 [] [])).
    vm_compute. reflexivity.
  - apply wait_ends_hang.
Qed.

(* =========================================================================
   The checker replay after ppoll
   ========================================================================= *)

Definition monitor_trace_c25 : SyscallInput * SyscallEffect :=
  (efd_read_in 4 8, mkEffect 8 [(0x10000, efd_one)] []).
Definition monitor_trace_c26 : SyscallInput * SyscallEffect :=
  (monitor_trace_call 94 0 0 0 0 0 0, mkEffect 0 [] []).

Definition monitor_trace_s25 : Model := monitor_trace_next monitor_trace_c25 monitor_trace_s24.
Definition monitor_trace_s26 : Model := monitor_trace_next monitor_trace_c26 monitor_trace_s25.

Definition monitor_trace_checked_calls : list (SyscallInput * SyscallEffect) :=
  [ monitor_trace_c01; monitor_trace_c02; monitor_trace_c03; monitor_trace_c04;
    monitor_trace_c05; monitor_trace_c06; monitor_trace_c07; monitor_trace_c08;
    monitor_trace_c09; monitor_trace_c10; monitor_trace_c11; monitor_trace_c12;
    monitor_trace_c13; monitor_trace_c14; monitor_trace_c15; monitor_trace_c16;
    monitor_trace_c17; monitor_trace_c18; monitor_trace_c19; monitor_trace_c20;
    monitor_trace_c21; monitor_trace_c22; monitor_trace_c23; monitor_trace_c25;
    monitor_trace_c26 ].

Example monitor_trace_has_25_checker_calls : length monitor_trace_checked_calls = 25%nat.
Proof. reflexivity. Qed.

(* =========================================================================
   One checker result per traced checker call
   ========================================================================= *)

Example monitor_trace_open_namespace :
  monitor_trace_check monitor_trace_c01 monitor_trace_s00 = CheckOk monitor_trace_s01 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_stat_ipc :
  monitor_trace_check monitor_trace_c02 monitor_trace_s01 = CheckOk monitor_trace_s02 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_stat_mnt :
  monitor_trace_check monitor_trace_c03 monitor_trace_s02 = CheckOk monitor_trace_s03 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_stat_net :
  monitor_trace_check monitor_trace_c04 monitor_trace_s03 = CheckOk monitor_trace_s04 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_stat_pid :
  monitor_trace_check monitor_trace_c05 monitor_trace_s04 = CheckOk monitor_trace_s05 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_stat_uts :
  monitor_trace_check monitor_trace_c06 monitor_trace_s05 = CheckOk monitor_trace_s06 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_close_namespace :
  monitor_trace_check monitor_trace_c07 monitor_trace_s06 = CheckOk monitor_trace_s07 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_capset :
  monitor_trace_check monitor_trace_c08 monitor_trace_s07 = CheckOk monitor_trace_s08 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_set_dumpable :
  monitor_trace_check monitor_trace_c09 monitor_trace_s08 = CheckOk monitor_trace_s09 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_set_pdeathsig :
  monitor_trace_check monitor_trace_c10 monitor_trace_s09 = CheckOk monitor_trace_s10 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_write_eventfd :
  monitor_trace_check monitor_trace_c11 monitor_trace_s10 = CheckOk monitor_trace_s11 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_close_eventfd :
  monitor_trace_check monitor_trace_c12 monitor_trace_s11 = CheckOk monitor_trace_s12 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_open_directory :
  monitor_trace_check monitor_trace_c13 monitor_trace_s12 = CheckOk monitor_trace_s13 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_fstat_directory :
  monitor_trace_check monitor_trace_c14 monitor_trace_s13 = CheckOk monitor_trace_s14 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_getfl_directory :
  monitor_trace_check monitor_trace_c15 monitor_trace_s14 = CheckOk monitor_trace_s15 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_mmap_directory_buffer :
  monitor_trace_check monitor_trace_c16 monitor_trace_s15 = CheckOk monitor_trace_s16 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_setfd_directory :
  monitor_trace_check monitor_trace_c17 monitor_trace_s16 = CheckOk monitor_trace_s17 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_getdents :
  monitor_trace_check monitor_trace_c18 monitor_trace_s17 = CheckOk monitor_trace_s18 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_close_proc :
  monitor_trace_check monitor_trace_c19 monitor_trace_s18 = CheckOk monitor_trace_s19 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_getdents_end :
  monitor_trace_check monitor_trace_c20 monitor_trace_s19 = CheckOk monitor_trace_s20 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_close_directory :
  monitor_trace_check monitor_trace_c21 monitor_trace_s20 = CheckOk monitor_trace_s21 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_munmap_directory_buffer :
  monitor_trace_check monitor_trace_c22 monitor_trace_s21 = CheckOk monitor_trace_s22 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_signalfd :
  monitor_trace_check monitor_trace_c23 monitor_trace_s22 = CheckOk monitor_trace_s23 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_read_eventfd :
  monitor_trace_check monitor_trace_c25 monitor_trace_s24 = CheckOk monitor_trace_s25 [].
Proof. vm_compute. reflexivity. Qed.

Example monitor_trace_exit_group :
  monitor_trace_check monitor_trace_c26 monitor_trace_s25 = CheckOk monitor_trace_s26 [].
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   The model-threaded replay
   ========================================================================= *)

Lemma monitor_trace_replays_to_exit :
  parent_trace_run monitor_trace_checked_calls monitor_trace_s00
  = Some monitor_trace_s26
  /\ (forall cfg,
        sstep_wcfg [] cfg waits_end
          (mkCfg monitor_trace_ppoll_ms monitor_trace_s23) []
          (SNext (mkCfg (advance_past_svc
            (apply_effect monitor_trace_ppoll_ms monitor_trace_ppoll_eff)) monitor_trace_s24)))
  /\ (forall cfg,
        sstep_wcfg [] cfg waits_may_hang
          (mkCfg monitor_trace_ppoll_ms monitor_trace_s23) [] SError).
Proof.
  split.
  - unfold monitor_trace_checked_calls.
    eapply parent_trace_run_step; [exact monitor_trace_open_namespace |].
    eapply parent_trace_run_step; [exact monitor_trace_stat_ipc |].
    eapply parent_trace_run_step; [exact monitor_trace_stat_mnt |].
    eapply parent_trace_run_step; [exact monitor_trace_stat_net |].
    eapply parent_trace_run_step; [exact monitor_trace_stat_pid |].
    eapply parent_trace_run_step; [exact monitor_trace_stat_uts |].
    eapply parent_trace_run_step; [exact monitor_trace_close_namespace |].
    eapply parent_trace_run_step; [exact monitor_trace_capset |].
    eapply parent_trace_run_step; [exact monitor_trace_set_dumpable |].
    eapply parent_trace_run_step; [exact monitor_trace_set_pdeathsig |].
    eapply parent_trace_run_step; [exact monitor_trace_write_eventfd |].
    eapply parent_trace_run_step; [exact monitor_trace_close_eventfd |].
    eapply parent_trace_run_step; [exact monitor_trace_open_directory |].
    eapply parent_trace_run_step; [exact monitor_trace_fstat_directory |].
    eapply parent_trace_run_step; [exact monitor_trace_getfl_directory |].
    eapply parent_trace_run_step; [exact monitor_trace_mmap_directory_buffer |].
    eapply parent_trace_run_step; [exact monitor_trace_setfd_directory |].
    eapply parent_trace_run_step; [exact monitor_trace_getdents |].
    eapply parent_trace_run_step; [exact monitor_trace_close_proc |].
    eapply parent_trace_run_step; [exact monitor_trace_getdents_end |].
    eapply parent_trace_run_step; [exact monitor_trace_close_directory |].
    eapply parent_trace_run_step; [exact monitor_trace_munmap_directory_buffer |].
    eapply parent_trace_run_step; [exact monitor_trace_signalfd |].
    eapply parent_trace_run_step; [exact monitor_trace_read_eventfd |].
    eapply parent_trace_run_step; [exact monitor_trace_exit_group |].
    reflexivity.
  - split; [exact monitor_trace_ppoll_steps_under_waits_end |
            exact monitor_trace_ppoll_is_error_under_waits_may_hang].
Qed.

(** Trace-call index, in order:

    01 openat: [monitor_trace_open_namespace].
    02-06 newfstatat: [monitor_trace_stat_ipc], [monitor_trace_stat_mnt],
       [monitor_trace_stat_net], [monitor_trace_stat_pid],
       [monitor_trace_stat_uts].
    07 close: [monitor_trace_close_namespace].
    08 capset: [monitor_trace_capset].
    09-10 prctl: [monitor_trace_set_dumpable], [monitor_trace_set_pdeathsig].
    11 write: [monitor_trace_write_eventfd].
    12 close: [monitor_trace_close_eventfd].
    13 openat: [monitor_trace_open_directory].
    14 fstat: [monitor_trace_fstat_directory].
    15 fcntl(F_GETFL): [monitor_trace_getfl_directory].
    16 mmap: [monitor_trace_mmap_directory_buffer].
    17 fcntl(F_SETFD): [monitor_trace_setfd_directory].
    18 getdents64: [monitor_trace_getdents].
    19 close: [monitor_trace_close_proc].
    20 getdents64: [monitor_trace_getdents_end].
    21 close: [monitor_trace_close_directory].
    22 munmap: [monitor_trace_munmap_directory_buffer].
    23 signalfd4: [monitor_trace_signalfd].
    24 ppoll: [monitor_trace_ppoll_steps_under_waits_end] and
       [monitor_trace_ppoll_is_error_under_waits_may_hang].
    25 read: [monitor_trace_read_eventfd].
    26 exit_group: [monitor_trace_exit_group].

    [monitor_trace_replays_to_exit] combines the two checker chains with the
    [ppoll] step at their common model state.  It does not claim the
    instruction-level links between the recorded system calls. *)

Print Assumptions monitor_trace_replays_to_exit.
