(** * LinuxProcessSem.Checks.Cases.Kernel.ProcsKill — kill (129) in the multi-process core

    Not part of the trusted specification: this file is QA on the
    definitions, in the sense of [Checks.Examples]'s header.  Its cases
    pin MODEL-INTERNAL STATE that no single-process run shows: which entry
    of a [Procs.pconfig] a [kill] ends, and that the other entry is left
    as it was.

    [Kernel.Signal.kill_spec] answers a [kill] that names the caller's own
    process id, behind the self-kill declaration
    ([State.in_selfkill_terminal]); [Checks.Cases.Kernel.Signal] pins that
    answer at one model.  Here the caller is the child entry of a
    two-entry table.  [kill] is class (A), private to the caller
    ([Procs.multiproc_private_sysnos]), so the core takes the released
    step as it stands: [Procs.pstep_other], and under [Ns.Ext.no_ext] its
    extension twin [Procs.px_other] over [Procs.xs_released] (that
    extension claims no call, so the released step answers).  The released
    step is [Run.sstep_cfg]'s killed arm.

    THE FIXTURE.  The root has key 1 and the child key 2, with the root as
    its parent.  A child's pid is its key: the core lets [getpid] pin a
    non-root entry's tid only at its key ([Procs.answer_ok_b]), so the
    child's model has its tid pinned at 2, as after its first [getpid].
    It declares the self-kill path ([State.with_selfkill_terminal]);
    [Procs.child_proc] copies the declaration from the parent at a clone,
    and the fixture writes it directly.  The root's machine has no call
    pending.

    THE POSITIVE CASE: the child at [kill(2, SIGKILL)] steps; the trace of
    the step is the one death [KillEv 9]; the child's entry is halted and
    killed by signal 9; the root's entry is unchanged.  Linux sends to a
    positive pid through [kill_proc_info] ([kill_something_info],
    kernel/signal.c:1585-1586, v6.18.46), and SIGKILL takes
    [complete_signal]'s fatal path (:1003-1025), which ends the target's
    thread group and no other.

    THE CONTROL: the child at [kill(1, SIGKILL)], its parent's pid.  The
    arm declines a signal to another process, so the released step is the
    error transition and the core lifts it to [PError]
    ([Procs.pstep_error], [Procs.px_error]). *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext.
From LinuxProcessSemantics.LinuxProcessSem Require Import Procs.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The fixture
   ========================================================================= *)

Definition pk_root : Pid := one_pid.
Definition pk_child : Pid := Z_to_bv 64 2.

(** The machine of an entry with no call pending. *)
Definition pk_idle_ms : machine_state := {|
  ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
  ms_pc_val := Z_to_bv 64 0x100;
  ms_svc_pending := None;
  ms_resv := None; ms_fcsr := Z_to_bv 32 0;
  ms_mem := fun _ => None; ms_rom := fun _ => None |}.

(** The machine at a [kill] ecall: number 129 pending, [pid] in a0 and
    [sig] in a1.  [kill] reads no memory. *)
Definition pk_kill_ms (pid sig : Z) : machine_state :=
  let base := {| ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
                 ms_pc_val := Z_to_bv 64 0x100;
                 ms_svc_pending := Some (Z_to_bv 64 129);
                 ms_resv := None; ms_fcsr := Z_to_bv 32 0;
                 ms_mem := fun _ => None; ms_rom := fun _ => None |} in
  set_reg (set_reg base (Z_to_bv 5 10) (Z_to_bv 64 pid))
          (Z_to_bv 5 11) (Z_to_bv 64 sig).

Definition pk_input : ProcInput :=
  mkProcInput [] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

Definition pk_base : Model := init_model [] 0 0 demo_sp demo_limit pk_input.

(** The child: tid pinned at its key, the self-kill path declared. *)
Definition pk_child_model : Model :=
  with_tid pk_child (with_selfkill_terminal true pk_base).

(** The shared state of a system that has entered no namespace, through
    [Procs.one_proc] rather than the record's constructor. *)
Definition pk_shared : shared := pcfg_shared (one_proc (mkCfg pk_idle_ms pk_base)).

Definition pk_root_entry : ProcessEntry :=
  mkEntry pk_root None pk_idle_ms (clear_shared pk_base) [] init_nsctx.

Definition pk_child_entry : ProcessEntry :=
  mkEntry pk_child (Some pk_root) (pk_kill_ms 2%Z 9%Z)
    (clear_shared pk_child_model) [] init_nsctx.

Definition pk_P : pconfig :=
  mkPCfg [(pk_root, pk_root_entry); (pk_child, pk_child_entry)] pk_root pk_shared.

(* =========================================================================
   The positive case: the child kills itself
   ========================================================================= *)

(** The child's released configuration, the shared state spliced in. *)
Definition pk_c : config := pe_cfg pk_shared pk_child_entry.

Definition pk_killed : Model := with_killed (Z_to_bv 64 9) (cfg_model pk_c).
Definition pk_c' : config := mkCfg (cfg_ms pk_c) pk_killed.
Definition pk_trace : list event := [KillEv (Z_to_bv 64 9) (m_fs pk_killed)].

(** The arm's answer at the child: the death by signal 9. *)
Lemma pk_check :
  check_syscall (sys_input [] (cfg_ms pk_c) (Z_to_bv 64 129))
    (mkEffect (Z_to_bv 64 0) [] []) (cfg_model pk_c)
  = CheckOk pk_killed [].
Proof. check_eq. Qed.

Lemma pk_sstep : forall cfg, sstep_cfg [] cfg pk_c pk_trace (SNext pk_c').
Proof.
  intros cfg.
  change pk_c with (mkCfg (cfg_ms pk_c) (cfg_model pk_c)).
  unfold pk_trace, pk_c'.
  change [KillEv (Z_to_bv 64 9) (m_fs pk_killed)]
    with ([] ++ [KillEv (Z_to_bv 64 9) (m_fs pk_killed)]).
  apply sstep_cfg_killed with (x8 := Z_to_bv 64 129)
                              (eff := mkEffect (Z_to_bv 64 0) [] []).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply check_syscall_ok_iff. exact pk_check.
  - vm_compute. reflexivity.
Qed.

Definition pk_P' : pconfig := absorb pk_P pk_child_entry pk_c'.

(** The step of the table: [Procs.pstep_other] at the child. *)
Theorem procs_kill_self_kills : forall cfg,
  pstep_at [] cfg pk_child pk_P pk_trace (PNext (absorb pk_P pk_child_entry pk_c')).
Proof.
  intros cfg.
  apply pstep_other with (e := pk_child_entry) (c' := pk_c').
  2: exact (pk_sstep cfg).
  all: vm_compute; reflexivity.
Qed.

(** The child's entry after the step is halted and killed by 9 ... *)
Example procs_kill_child_killed :
  option_map (fun e => (m_halted (pe_model e), m_killed (pe_model e)))
    (look pk_P' pk_child)
  = Some (Some (Z_to_bv 64 9), Some (Z_to_bv 64 9)).
Proof. check_eq. Qed.

(** ... and the root's entry is the one it was. *)
Example procs_kill_root_unchanged : look pk_P' pk_root = look pk_P pk_root.
Proof. vm_compute. reflexivity. Qed.

(** The same step under [Ns.Ext.no_ext], through [Procs.px_other]: the
    extension claims nothing, so [Procs.xs_released] carries the released
    step, and the namespace context and state are unchanged. *)
Theorem procs_kill_self_kills_x : forall cenv cfg,
  pstep_x_at no_ext cenv [] cfg pk_child pk_P pk_trace
    (PNext (absorb_x pk_P pk_child_entry pk_c'
              (pe_nsctx pk_child_entry) (sh_ns (pcfg_shared pk_P)))).
Proof.
  intros cenv cfg.
  apply px_other with (e := pk_child_entry) (c' := pk_c').
  2: apply xs_released; [vm_compute; reflexivity | exact (pk_sstep cfg)].
  all: vm_compute; reflexivity.
Qed.

(* =========================================================================
   The control: the child names its parent
   ========================================================================= *)

Definition pkc_child_entry : ProcessEntry :=
  mkEntry pk_child (Some pk_root) (pk_kill_ms 1%Z 9%Z)
    (clear_shared pk_child_model) [] init_nsctx.

Definition pkc_P : pconfig :=
  mkPCfg [(pk_root, pk_root_entry); (pk_child, pkc_child_entry)] pk_root pk_shared.

Definition pkc_c : config := pe_cfg pk_shared pkc_child_entry.

(** Pid 1 is not the caller's: the arm declines. *)
Lemma pkc_check :
  check_syscall (sys_input [] (cfg_ms pkc_c) (Z_to_bv 64 129))
    (mkEffect (Z_to_bv 64 0) [] []) (cfg_model pkc_c)
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Lemma pkc_sstep : forall cfg, sstep_cfg [] cfg pkc_c [] SError.
Proof.
  intros cfg.
  change pkc_c with (mkCfg (cfg_ms pkc_c) (cfg_model pkc_c)).
  apply sstep_cfg_syscall_unmodeled with (x8 := Z_to_bv 64 129).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply check_syscall_sound_unmodeled
      with (eff := mkEffect (Z_to_bv 64 0) [] []).
    exact pkc_check.
Qed.

Theorem procs_kill_parent_errors : forall cfg,
  pstep_at [] cfg pk_child pkc_P [] PError.
Proof.
  intros cfg.
  apply pstep_error with (e := pkc_child_entry).
  2: exact (pkc_sstep cfg).
  all: vm_compute; reflexivity.
Qed.

Theorem procs_kill_parent_errors_x : forall cenv cfg,
  pstep_x_at no_ext cenv [] cfg pk_child pkc_P [] PError.
Proof.
  intros cenv cfg.
  apply px_error with (e := pkc_child_entry)
                      (ctx' := pe_nsctx pkc_child_entry)
                      (st' := sh_ns (pcfg_shared pkc_P)).
  2: apply xs_released; [vm_compute; reflexivity | exact (pkc_sstep cfg)].
  all: vm_compute; reflexivity.
Qed.
