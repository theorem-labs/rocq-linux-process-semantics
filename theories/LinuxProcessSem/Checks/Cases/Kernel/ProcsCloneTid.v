(** * LinuxProcessSem.Checks.Cases.Kernel.ProcsCloneTid — clone (220) with the tid words and clone3 (435) with a stack, in the single-process step and the multi-process core

    One [clone] of a caller in the released world, with
    [SIGCHLD | CLONE_PARENT_SETTID | CLONE_CHILD_SETTID | CLONE_SETTLS]
    and no [CLONE_VM] (Linux v6.18.46):
    - the single-process step ([Run.sstep_cfg]) writes the pid it returns
      at the parent-tid pointer a2 (kernel/fork.c:2626-2627);
    - the child the core makes ([Procs.child_ms]) has the caller's
      registers with tp = a3 and a0 = 0 (arch/riscv/kernel/process.c:253-255),
      the caller's memory as the call began, so a2 still holds 0 there
      (fork.c:1547-1549 copies the mm before 2626), and its own pid at the
      child-tid pointer a4 (kernel/sched/core.c:5272-5273);
    - when the namespace extension gives the call a return value of its
      own, the core writes that value at a2 instead
      ([Procs.clone_parent_rewrite], fork.c:2623-2627), and a store of it
      the model cannot account is the premise of the error step
      [Procs.px_clone_store_refuse].
    And one [clone3] with a stack: the child's sp is stack + stack_size
    (fork.c:2845-2847). *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem Require Import Procs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Tables.
Import ListNotations.
Open Scope bv_scope.

(** Four zero bytes at the parent-tid pointer 0x2000 and at the
    child-tid pointer 0x3000, in the caller's writable memory. *)
Definition ct_mem : word -> option byte :=
  fun a => if (((0x2000 <=? bv_unsigned a) && (bv_unsigned a <? 0x2004))
               || ((0x3000 <=? bv_unsigned a) && (bv_unsigned a <? 0x3004)))%Z
           then Some (Z_to_bv 8 0) else None.

Definition ct_flags : Z :=
  (SIGCHLD + CLONE_PARENT_SETTID + CLONE_CHILD_SETTID + CLONE_SETTLS)%Z.

(** The machine at the [clone] ecall: a0 the flag word, a1 = 0 (the
    caller's stack), a2 = 0x2000, a3 = 0x1000 (the tls), a4 = 0x3000. *)
Definition ct_ms : machine_state :=
  let base := {| ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
                 ms_pc_val := Z_to_bv 64 0x100;
                 ms_svc_pending := Some (Z_to_bv 64 220);
                 ms_resv := None; ms_fcsr := Z_to_bv 32 0;
                 ms_mem := ct_mem; ms_rom := fun _ => None |} in
  set_reg (set_reg (set_reg (set_reg base (Z_to_bv 5 10) (Z_to_bv 64 ct_flags))
                            (Z_to_bv 5 12) (Z_to_bv 64 0x2000))
                   (Z_to_bv 5 13) (Z_to_bv 64 0x1000))
          (Z_to_bv 5 14) (Z_to_bv 64 0x3000).

Definition ct_input : ProcInput :=
  mkProcInput [] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

Definition ct_model : Model := init_model [] 0 0 demo_sp demo_limit ct_input.

Definition ct_c : config := mkCfg ct_ms ct_model.

(** The pid the step returns, and its answer: the pid, with its four
    bytes at a2. *)
Definition ct_pid : word := Z_to_bv 64 4242.

Definition ct_eff : SyscallEffect :=
  mkEffect ct_pid [(Z_to_bv 64 0x2000, le32_bytes ct_pid)] [].

Definition ct_model' : Model := clone_child_made ct_pid ct_model.

Definition ct_c' : config := mkCfg (advance_past_svc (apply_effect ct_ms ct_eff)) ct_model'.

Lemma ct_check :
  check_syscall (sys_input [] ct_ms (Z_to_bv 64 220)) ct_eff ct_model = CheckOk ct_model' [].
Proof. vm_compute. reflexivity. Qed.

(** The answer without the store is refused: the caller's memory written
    by the call itself is in the effect. *)
Example ct_no_store_refused :
  check_syscall (sys_input [] ct_ms (Z_to_bv 64 220)) (mkEffect ct_pid [] []) ct_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** THE SINGLE-PROCESS STEP of the call: a successful clone with
    [CLONE_PARENT_SETTID] writes the returned pid at a2. *)
Lemma ct_sstep : forall cfg, sstep_cfg [] cfg ct_c [] (SNext ct_c').
Proof.
  intros cfg. unfold ct_c, ct_c'.
  apply sstep_cfg_syscall with (x8 := Z_to_bv 64 220) (model' := ct_model').
  - vm_compute. reflexivity.
  - reflexivity.
  - apply check_syscall_sound_ok. exact ct_check.
  - intros (_ & Hr & _). vm_compute in Hr. discriminate Hr.
  - vm_compute. reflexivity.
  - apply materialize_model_accesses_no_lazy. vm_compute. reflexivity.
Qed.

Example clone_parent_settid_single_process :
  map (fun a => option_map bv_unsigned (ms_mem (cfg_ms ct_c') (Z_to_bv 64 a)))
      [0x2000; 0x2001; 0x2002; 0x2003]%Z
  = [Some 0x92; Some 0x10; Some 0; Some 0]%Z
  /\ bv_unsigned (ms_gpr (cfg_ms ct_c') 0) = 4242%Z
  /\ clone_success_b ct_c ct_c' = true.
Proof. vm_compute. repeat split. Qed.

(** THE CHILD THE CORE MAKES: a0 = 0, tp = 0x1000, the pc and the
    pending-call state of the caller's successor (the state after the
    ecall), the caller's memory as the call began at a2 (0, not the
    pid), and its own pid at a4. *)
Example clone_child_registers_and_memory :
  bv_unsigned (ms_gpr (child_ms ct_c ct_c') 0) = 0%Z
  /\ bv_unsigned (ms_reg (child_ms ct_c ct_c') (Z_to_bv 5 4)) = 0x1000%Z
  /\ bv_unsigned (ms_pc_val (child_ms ct_c ct_c')) = bv_unsigned (ms_pc_val (cfg_ms ct_c'))
  /\ ms_svc_pending (child_ms ct_c ct_c') = ms_svc_pending (cfg_ms ct_c')
  /\ map (fun a => option_map bv_unsigned (ms_mem (child_ms ct_c ct_c') (Z_to_bv 64 a)))
         [0x2000; 0x2001; 0x2002; 0x2003; 0x3000; 0x3001; 0x3002; 0x3003]%Z
     = [Some 0; Some 0; Some 0; Some 0; Some 0x92; Some 0x10; Some 0; Some 0]%Z.
Proof. vm_compute. repeat split. Qed.

(** THE SAME CALL ON A TABLE THAT HOLDS A LIVE INHERITED FILE (fd 3, the
    bytes "key\n" at offset 1) AND A NON-BLOCKING EVENTFD (fd 4, counter
    5).  The caller keeps [Kernel.Fork.clone_child_made]'s table: fd 3
    without its offset, fd 4 the shared kind.  The child the core makes
    ([Procs.child_entry]) makes its own [CLONE_CHILD_SETTID] store, whose
    accounting on the caller's model succeeds, so its model is the
    accounted one ([Procs.child_model]), and its table is the
    caller's table before the call with only the sharing applied: fd 3
    keeps its offset, fd 4 is the shared kind.  THE CONTROLS: the child's
    table is neither the table before the call nor the caller's new
    table. *)
Definition ctm_fds : list (word * FdEntry) :=
  [(Z_to_bv 64 3, FdOpaque (OInherited (Some ([107; 101; 121; 10], 1))));
   (Z_to_bv 64 4, FdEventfd (mkEventfdCtx 5 false true))].

Definition ctm_child_fds : list (word * FdEntry) :=
  [(Z_to_bv 64 3, FdOpaque (OInherited (Some ([107; 101; 121; 10], 1))));
   (Z_to_bv 64 4, FdOpaque (OEventFd (Z_to_bv 64 0x800)))].

Definition ctm_model : Model := with_fds ctm_fds ct_model.

Definition ctm_c : config := mkCfg ct_ms ctm_model.

Definition ctm_c' : config :=
  mkCfg (advance_past_svc (apply_effect ct_ms ct_eff)) (clone_child_made ct_pid ctm_model).

Definition ctm_parent : ProcessEntry :=
  mkEntry (Z_to_bv 64 1) None ct_ms ctm_model [] Tables.init_nsctx.

Example clone_child_settid_mixed_table :
  check_syscall (sys_input [] ct_ms (Z_to_bv 64 220)) ct_eff ctm_model
  = CheckOk (clone_child_made ct_pid ctm_model) []
  /\ m_fds (clone_child_made ct_pid ctm_model)
     = [(Z_to_bv 64 3, FdOpaque (OInherited None));
        (Z_to_bv 64 4, FdOpaque (OEventFd (Z_to_bv 64 0x800)))]
  /\ child_tid_store ctm_c ctm_c' <> []
  /\ materialize_model_accesses ctm_model (write_accesses (child_tid_store ctm_c ctm_c')) <> None
  /\ m_fds (pe_model (child_entry ctm_parent ctm_c ctm_c' ct_pid)) = ctm_child_fds
  /\ ctm_child_fds <> ctm_fds
  /\ ctm_child_fds <> m_fds (clone_child_made ct_pid ctm_model).
Proof.
  repeat match goal with |- _ /\ _ => split end;
    [ vm_compute; reflexivity | vm_compute; reflexivity
    | intros H; vm_compute in H; discriminate H
    | intros H; vm_compute in H; discriminate H
    | vm_compute; reflexivity
    | intros H; vm_compute in H; discriminate H
    | intros H; vm_compute in H; discriminate H ].
Qed.

(** The extension gives the call a return value of its own, 77: the
    caller's four bytes at a2 hold 77 ([Procs.clone_parent_rewrite]), and
    with the released pid kept nothing is rewritten. *)
Example clone_parent_settid_extension_value :
  match clone_parent_rewrite [] ct_c (with_ret ct_c' (Some 77%Z)) (Some 77%Z) with
  | Some c2 => map (fun a => option_map bv_unsigned (ms_mem (cfg_ms c2) (Z_to_bv 64 a)))
                   [0x2000; 0x2001; 0x2002; 0x2003]%Z
  | None => []
  end = [Some 77; Some 0; Some 0; Some 0]%Z
  /\ clone_parent_rewrite [] ct_c ct_c' None = Some ct_c'.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** A PARENT-TID STORE THE MODEL CANNOT ACCOUNT, in the released step:
    the caller's model holds a MAP_NORESERVE page at a2 that its backing
    limit (0 here) cannot charge.  The answer with the store is the
    released spec's, and its accounting fails, so the step is the error
    transition ([Run.sstep_cfg_syscall_materialization_fault]).  The
    word holds no [CLONE_CHILD_SETTID], so no child store is asked. *)
Definition ct_lazy_model : Model :=
  with_vm_backing [(Z_to_bv 64 0x2000, Z_to_bv 64 0x1000)] []
    (mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] None None None).

Definition pt_ms : machine_state :=
  set_reg ct_ms (Z_to_bv 5 10) (Z_to_bv 64 (SIGCHLD + CLONE_PARENT_SETTID)).

Definition pt_model' : Model := clone_child_made ct_pid ct_lazy_model.

Lemma pt_check :
  check_syscall (sys_input [] pt_ms (Z_to_bv 64 220)) ct_eff ct_lazy_model
  = CheckOk pt_model' [].
Proof. vm_compute. reflexivity. Qed.

Lemma clone_parent_settid_unaccounted_step : forall cfg,
  sstep_cfg [] cfg (mkCfg pt_ms ct_lazy_model) [] SError.
Proof.
  intros cfg.
  apply sstep_cfg_syscall_materialization_fault with
    (x8 := Z_to_bv 64 220) (eff := ct_eff) (model' := pt_model') (evs := []).
  - vm_compute. reflexivity.
  - reflexivity.
  - apply check_syscall_sound_ok. exact pt_check.
  - intros (_ & Hr & _). vm_compute in Hr. discriminate Hr.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(** The same page under [Procs.clone_parent_rewrite], ON A SYNTHETIC
    CONFIGURATION: the caller's successor paired with [ct_lazy_model],
    which no step reaches, since the released step above already
    accounts the same four bytes before the core rewrites them.  It shows
    only that the rewrite of the extension's value 77 is then [None], the
    premise of the error step [Procs.px_clone_store_refuse]. *)
Example clone_parent_settid_unaccounted :
  clone_parent_rewrite [] ct_c (with_ret (mkCfg (cfg_ms ct_c') ct_lazy_model) (Some 77%Z))
    (Some 77%Z) = None.
Proof. vm_compute. reflexivity. Qed.

(** [clone3] (435) with no flag, stack 0x8000 and stack_size 0x1000: the
    child's sp is the record's stack, 0x9000 (kernel/fork.c:2845-2847;
    arch/riscv/kernel/process.c:251-252), and the namespace extension is
    given that record ([Procs.clone_in_of]). *)
Definition c3_mem : word -> option byte :=
  let bs := flat_map (Z_to_le_bytes 8)
              [0; 0; 0; 0; SIGCHLD; 0x8000; 0x1000; 0; 0; 0; 0]%Z in
  fun a => let off := (bv_unsigned a - 0x1000)%Z in
           if ((0 <=? off)%Z && (off <? CLONE_ARGS_SIZE)%Z)%bool
           then nth_error bs (Z.to_nat off) else None.

(** The machine at the [clone3] ecall: a0 the struct at 0x1000, a1 its
    size. *)
Definition c3_ms : machine_state :=
  let base := {| ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
                 ms_pc_val := Z_to_bv 64 0x100;
                 ms_svc_pending := Some (Z_to_bv 64 435);
                 ms_resv := None; ms_fcsr := Z_to_bv 32 0;
                 ms_mem := c3_mem; ms_rom := fun _ => None |} in
  set_reg (set_reg base (Z_to_bv 5 10) (Z_to_bv 64 0x1000))
          (Z_to_bv 5 11) (Z_to_bv 64 CLONE_ARGS_SIZE).

Example clone3_child_sp :
  bv_unsigned (ms_reg (child_ms (mkCfg c3_ms ct_model) (mkCfg c3_ms ct_model)) (Z_to_bv 5 2))
  = 0x9000%Z
  /\ match clone_in_of (mkCfg c3_ms ct_model) with
     | CiArgs r => bv_unsigned (cla_stack r)
     | CiNoArgs => 0%Z
     end = 0x9000%Z.
Proof. split; vm_compute; reflexivity. Qed.
