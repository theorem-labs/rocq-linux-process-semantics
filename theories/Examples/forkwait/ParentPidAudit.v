(** * Examples.forkwait.ParentPidAudit — the root-parent repair keeps this claim

    This audit belongs to the examples theory, which depends on the core.
    Its output gives the actual type and primitive assumptions of the halting
    proof alongside the core's parent-pid regressions. *)

From LinuxProcessSemantics.Examples.forkwait Require Import Halts.

Goal True. idtac "FORKWAIT_PARENT_PID_AUDIT_BEGIN". exact I. Qed.
Check forkwait_halts_proved.
Print Assumptions forkwait_halts_proved.
Goal True. idtac "FORKWAIT_PARENT_PID_AUDIT_END". exact I. Qed.

Goal True. idtac "FORKWAIT_PARENT_FRAME_CLOSURE_BEGIN". exact I. Qed.
Check fw_entry_instr_step.
Print Assumptions fw_entry_instr_step.
Check fw_entry_left_ppid_blind.
Print Assumptions fw_entry_left_ppid_blind.
Check MustExitP.pmeasure_absorb_lt.
Print Assumptions MustExitP.pmeasure_absorb_lt.
Goal True. idtac "FORKWAIT_PARENT_FRAME_CLOSURE_END". exact I. Qed.
