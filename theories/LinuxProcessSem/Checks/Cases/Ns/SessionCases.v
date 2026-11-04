(** * LinuxProcessSem.Checks.Cases.Ns.SessionCases — setsid in the namespace model

    The examples follow bubblewrap 0.13.1's setup child when it makes a new
    session: the child that [UtsCases] clones with a new user, mount, UTS,
    IPC, pid and network namespace is pid 1 of its new pid namespace, and
    its [setsid()] answers 1 ([Task.setsid_arm]; Linux v6.18.46,
    kernel/sys.c:1268-1301).  Around it: a second call, a task in the
    host's pid namespace, a task with no pid in its own namespace, and the
    admission while bubblewrap's parent lives. *)

From Stdlib Require Import ZArith List Bool PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Task Spec.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Ns Require UtsCases.
Import ListNotations.
Open Scope Z_scope.

Definition setsid_call : SyscallInput :=
  mkInput (Z_to_bv 64 157) (map (Z_to_bv 64) [0; 0; 0; 0; 0; 0]) (fun _ => None) (fun _ => None).

(** Outside the released world the namespace model answers 157 with
    [setsid_arm]. *)
Lemma ns_spec_157 : forall i m ctx st o,
  flat_view ctx st = false -> ns_sysno i = 157 ->
  ns_spec i m ctx st o <-> setsid_arm i m ctx st o.
Proof. intros i m ctx st o Hf Hn. unfold ns_spec. rewrite Hf, Hn. reflexivity. Qed.

Definition m0 : Model := UtsCases.m0.
Definition c_ctx : NsCtx := UtsCases.c_ctx.
Definition c_st : NsState := UtsCases.c_st.

(** [C]'s state carries the default launch value: no environment reaper
    calls [setpgid] on [C] before its [setsid]. *)
Example c_st_launch_default : env_foreign_pgroups (ns_env c_st) = false.
Proof. vm_compute. reflexivity. Qed.

(** bubblewrap's [setsid()] in [C], pid 1 of the pid namespace the clone
    made: no session led yet, and no process group can be 1 there (no
    modelled call makes one, and the launch value [env_foreign_pgroups]
    is its default [false]), so the answer is 1 and only 1, and the
    leader bit is set. *)
Definition c_setsid : ext_outcome :=
  ns_ret (Z_to_bv 64 1) (with_setsid_succeeded m0) c_ctx c_st.

Example bwrap_setsid_exact : forall o,
  ns_spec setsid_call m0 c_ctx c_st o <-> o = c_setsid.
Proof.
  intros o. eapply iff_trans; [apply ns_spec_157; vm_compute; reflexivity|].
  unfold setsid_arm.
  replace (m_setsid_succeeded m0) with false by (vm_compute; reflexivity).
  replace (task_pid c_ctx) with (Some 1) by (vm_compute; reflexivity).
  replace (pidns_made c_st (cx_pidns c_ctx)) with true by (vm_compute; reflexivity).
  replace (env_foreign_pgroups (ns_env c_st)) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

(** A second [setsid()] of the same process: EPERM, and only EPERM
    ([signal->leader], kernel/sys.c:1278-1279). *)
Example bwrap_setsid_again_eperm : forall o,
  ns_spec setsid_call (with_setsid_succeeded m0) c_ctx c_st o
  <-> o = ns_errno EPERM (with_setsid_succeeded m0) c_ctx c_st.
Proof.
  intros o. eapply iff_trans; [apply ns_spec_157; vm_compute; reflexivity|].
  unfold setsid_arm.
  replace (m_setsid_succeeded (with_setsid_succeeded m0)) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

(** A task in the host's pid namespace (pid 136 there) whose user
    namespace is [C]'s, so outside the released world: whether a live
    task's process group is 136 is the environment's, so EPERM and the
    pid are both admitted, as for the released [setsid]. *)
Definition h_ctx : NsCtx := with_pids (with_user_ns init_nsctx 2%positive) [(1%positive, 136)].

Example host_pidns_setsid_over : forall o,
  ns_spec setsid_call m0 h_ctx c_st o
  <-> o = ns_errno EPERM m0 h_ctx c_st
      \/ o = ns_ret (Z_to_bv 64 136) (with_setsid_succeeded m0) h_ctx c_st.
Proof.
  intros o. eapply iff_trans; [apply ns_spec_157; vm_compute; reflexivity|].
  unfold setsid_arm.
  replace (m_setsid_succeeded m0) with false by (vm_compute; reflexivity).
  replace (task_pid h_ctx) with (Some 136) by (vm_compute; reflexivity).
  replace (pidns_made c_st (cx_pidns h_ctx)) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

(** A task with no pid in its own pid namespace is not one the model
    holds: the call declines. *)
Example no_pid_setsid_declines : forall o,
  ns_spec setsid_call m0 (with_pids c_ctx []) c_st o <-> o = EUnmodeled.
Proof.
  intros o. eapply iff_trans; [apply ns_spec_157; vm_compute; reflexivity|].
  unfold setsid_arm.
  replace (m_setsid_succeeded m0) with false by (vm_compute; reflexivity).
  replace (task_pid (with_pids c_ctx [])) with (@None Z) by (vm_compute; reflexivity).
  reflexivity.
Qed.

(** The same call under the launch value [env_foreign_pgroups = true]: a
    reaper outside the model may have made a process group of [C]'s pid
    after [C]'s modelled parent exited ([setpgid], kernel/sys.c:1144-1150),
    so EPERM (kernel/sys.c:1284-1285) is admitted beside the success. *)
Definition c_st_foreign : NsState :=
  with_env c_st (env_with_foreign_pgroups (ns_env c_st) true).

Example foreign_pgroups_setsid_over : forall o,
  ns_spec setsid_call m0 c_ctx c_st_foreign o
  <-> o = ns_errno EPERM m0 c_ctx c_st_foreign
      \/ o = ns_ret (Z_to_bv 64 1) (with_setsid_succeeded m0) c_ctx c_st_foreign.
Proof.
  intros o. eapply iff_trans; [apply ns_spec_157; vm_compute; reflexivity|].
  unfold setsid_arm.
  replace (m_setsid_succeeded m0) with false by (vm_compute; reflexivity).
  replace (task_pid c_ctx) with (Some 1) by (vm_compute; reflexivity).
  replace (pidns_made c_st_foreign (cx_pidns c_ctx)) with true by (vm_compute; reflexivity).
  replace (env_foreign_pgroups (ns_env c_st_foreign)) with true by (vm_compute; reflexivity).
  reflexivity.
Qed.

(** While bubblewrap's parent lives, the namespace model admits [C]'s
    setsid ([Spec.ns_multiproc]). *)
Example bwrap_setsid_multiproc : ext_multiproc ns_ext setsid_call m0 c_ctx c_st = true.
Proof. vm_compute. reflexivity. Qed.
