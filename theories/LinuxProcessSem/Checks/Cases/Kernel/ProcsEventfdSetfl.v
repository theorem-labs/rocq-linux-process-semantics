(** * LinuxProcessSem.Checks.Cases.Kernel.ProcsEventfdSetfl — F_SETFL on a shared eventfd in the multi-process core

    Not part of the trusted specification: this file is QA on the
    definitions, in the sense of [Checks.Examples]'s header.  Its cases
    pin the wiring of [Procs.eventfd_setfl_nb_change_b], the eventfd part
    of [Procs.peer_refused_b], at a concrete two-entry table: the argument
    order, the bit, and the more-than-one-entry test.
    [Checks.ProcsPeerGates.eventfd_setfl_refused_iff] states the gate for
    every configuration; these cases run it.

    A successful clone turns every eventfd of the caller into the shared
    kind ([State.OEventFd w], [Kernel.Fork.share_eventfds]): parent and
    child then hold one open file description, and Linux keeps its
    O_NONBLOCK bit in the one [f_flags] both read ([setfl], fs/fcntl.c,
    v6.18.46).  The shared kind's F_SETFL arm ([Fs.Fcntl.oeventfd_setfl])
    records the bit in the caller's entry only.  So while the other entry
    lives, an F_SETFL that would change the bit is refused, and one that
    keeps it changes nothing the other entry reads and is answered.

    THE FIXTURE.  Before the clone the root holds two eventfds: fd 3,
    made blocking, and fd 4, made with EFD_NONBLOCK.  After it the root's
    model is [Kernel.Fork.clone_child_made] of that model and the child's
    table is [share_eventfds] of the same table, so both hold fd 3 as
    [OEventFd 0] and fd 4 as [OEventFd 0x800] (O_NONBLOCK).  The fixture
    writes the two entries directly, as [Checks.Cases.Kernel.ProcsKill]
    does.  The child has no call pending; the root is at
    [fcntl(fd, F_SETFL, arg)]: number 25, [fd] in a0, [F_SETFL] in a1 and
    [arg] in a2.

    THE CASES.
    - fcntl(3, F_SETFL, O_NONBLOCK) sets the bit fd 3 lacks: refused
      ([Procs.pstep_peer_refuse]), and no step has a successor.
    - fcntl(4, F_SETFL, 0) clears the bit fd 4 has: refused the same way.
    THE CONTROLS.
    - fcntl(4, F_SETFL, O_NONBLOCK) keeps fd 4's bit while a2 has it set:
      answered with 0 through [Procs.pstep_other], with fd 4 unchanged.
      A gate that read only a2's bit would refuse it.
    - fcntl(3, F_SETFL, O_NONBLOCK) with the root alone in the table: the
      same call by the same entry is answered with 0, and fd 3 now holds
      the bit.  The table differs from the refusing one only by the
      child's entry, the one thing besides the call that the gate reads. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs ProcsPeerGates.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext.
From LinuxProcessSemantics.LinuxProcessSem Require Import Procs.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The fixture
   ========================================================================= *)

Definition ef_root : Pid := one_pid.
Definition ef_child : Pid := Z_to_bv 64 2.

(** The machine of an entry with no call pending. *)
Definition ef_idle_ms : machine_state := {|
  ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
  ms_pc_val := Z_to_bv 64 0x100;
  ms_svc_pending := None;
  ms_resv := None; ms_fcsr := Z_to_bv 32 0;
  ms_mem := fun _ => None; ms_rom := fun _ => None |}.

(** The machine at [fcntl(fd, F_SETFL, arg)]: number 25 pending, [fd] in
    a0, [F_SETFL] in a1, [arg] in a2.  F_SETFL reads no memory. *)
Definition ef_fcntl_ms (fd arg : Z) : machine_state :=
  let base := {| ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
                 ms_pc_val := Z_to_bv 64 0x100;
                 ms_svc_pending := Some (Z_to_bv 64 25);
                 ms_resv := None; ms_fcsr := Z_to_bv 32 0;
                 ms_mem := fun _ => None; ms_rom := fun _ => None |} in
  set_reg (set_reg (set_reg base (Z_to_bv 5 10) (Z_to_bv 64 fd))
                   (Z_to_bv 5 11) F_SETFL)
          (Z_to_bv 5 12) (Z_to_bv 64 arg).

Definition ef_input : ProcInput :=
  mkProcInput [] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

Definition ef_base : Model := init_model [] 0 0 demo_sp demo_limit ef_input.

(** The root before the clone: fd 3 a blocking eventfd, fd 4 one made
    with EFD_NONBLOCK, both with counter 0. *)
Definition ef_pre : Model :=
  with_fds (fd_insert (fd_insert (m_fds ef_base)
                         (Z_to_bv 64 3) (FdEventfd (mkEventfdCtx 0 false false)))
              (Z_to_bv 64 4) (FdEventfd (mkEventfdCtx 0 false true)))
    ef_base.

(** After the clone: the root's model as the clone leaves it, and the
    child's table, [share_eventfds] of the root's table before the call. *)
Definition ef_root_model : Model := clone_child_made ef_child ef_pre.
Definition ef_child_model : Model := with_fds (share_eventfds (m_fds ef_pre)) ef_pre.

(** Both tables hold the shared kind, fd 3 without O_NONBLOCK and fd 4
    with it. *)
Example ef_fixture_shared :
  fd_lookup (m_fds ef_root_model) (Z_to_bv 64 3) = Some (FdOpaque (OEventFd (Z_to_bv 64 0)))
  /\ fd_lookup (m_fds ef_root_model) (Z_to_bv 64 4) = Some (FdOpaque (OEventFd (Z_to_bv 64 0x800)))
  /\ fd_lookup (m_fds ef_child_model) (Z_to_bv 64 3) = Some (FdOpaque (OEventFd (Z_to_bv 64 0)))
  /\ fd_lookup (m_fds ef_child_model) (Z_to_bv 64 4) = Some (FdOpaque (OEventFd (Z_to_bv 64 0x800))).
Proof. repeat split; check_eq. Qed.

(** The shared state of a system that has entered no namespace, through
    [Procs.one_proc] rather than the record's constructor. *)
Definition ef_shared : shared := pcfg_shared (one_proc (mkCfg ef_idle_ms ef_pre)).

(** The root at [fcntl(fd, F_SETFL, arg)]. *)
Definition ef_root_at (fd arg : Z) : ProcessEntry :=
  mkEntry ef_root None (ef_fcntl_ms fd arg) (clear_shared ef_root_model) [] init_nsctx.

Definition ef_child_entry : ProcessEntry :=
  mkEntry ef_child (Some ef_root) ef_idle_ms (clear_shared ef_child_model) [] init_nsctx.

(** The two-entry table, and the root alone. *)
Definition ef_P2 (fd arg : Z) : pconfig :=
  mkPCfg [(ef_root, ef_root_at fd arg); (ef_child, ef_child_entry)] ef_root ef_shared.
Definition ef_P1 (fd arg : Z) : pconfig :=
  mkPCfg [(ef_root, ef_root_at fd arg)] ef_root ef_shared.

(* =========================================================================
   The answered step, for the controls
   ========================================================================= *)

Definition ef_eff : SyscallEffect := mkEffect (Z_to_bv 64 0) [] [].

(** The model the fcntl arm answers 0 with at [c], and the model after
    the effect's accesses are materialized.  The controls below pin both
    by computation: the arm answers ([CheckOk]) and the accesses succeed. *)
Definition ef_checked (c : config) : Model :=
  match check_syscall (sys_input [] (cfg_ms c) (Z_to_bv 64 25)) ef_eff (cfg_model c) with
  | CheckOk m _ => m
  | _ => cfg_model c
  end.

Definition ef_next_model (c : config) : Model :=
  match materialize_model_accesses (ef_checked c) (syscall_effect_accesses ef_eff) with
  | Some m => m
  | None => ef_checked c
  end.

Definition ef_next (c : config) : config :=
  mkCfg (advance_past_svc (apply_effect (cfg_ms c) ef_eff)) (ef_next_model c).

(** The released step answering 0 at [c], from its computable premises. *)
Lemma ef_sstep : forall cfg c,
  m_halted (cfg_model c) = None ->
  ms_svc_pending (cfg_ms c) = Some (Z_to_bv 64 25) ->
  check_syscall (sys_input [] (cfg_ms c) (Z_to_bv 64 25)) ef_eff (cfg_model c)
    = CheckOk (ef_checked c) [] ->
  refusal_b (sys_input [] (cfg_ms c) (Z_to_bv 64 25)) (cfg_model c) (eff_ret ef_eff) = false ->
  m_halted (ef_checked c) = None ->
  materialize_model_accesses (ef_checked c) (syscall_effect_accesses ef_eff)
    = Some (ef_next_model c) ->
  sstep_cfg [] cfg c [] (SNext (ef_next c)).
Proof.
  intros cfg [ms m] Hh Hs Hc Hr Hh' Hm. cbn [cfg_ms cfg_model] in Hh, Hs, Hc, Hr.
  unfold ef_next. cbn [cfg_ms].
  apply sstep_cfg_syscall with (x8 := Z_to_bv 64 25) (eff := ef_eff)
                               (model' := ef_checked (mkCfg ms m)).
  - exact Hh.
  - exact Hs.
  - apply check_syscall_ok_iff. exact Hc.
  - apply spurious_refusal_not_refusal. exact Hr.
  - exact Hh'.
  - exact Hm.
Qed.

(* =========================================================================
   The refusals: a change of the bit while the child lives
   ========================================================================= *)

(** fcntl(3, F_SETFL, O_NONBLOCK): fd 3 lacks the bit, so the call would
    set it.  The gate fires ... *)
Example ef_set_gate_fires :
  eventfd_setfl_nb_change_b (ef_root_at 3 0x800) = true
  /\ peer_refused_b (ef_P2 3 0x800) (ef_root_at 3 0x800) = true.
Proof. split; vm_compute; reflexivity. Qed.

(** ... the entry takes the refusal, and no step has a successor. *)
Theorem procs_eventfd_setfl_set_refused : forall cfg,
  pstep_at [] cfg ef_root (ef_P2 3 0x800) [] PError
  /\ (forall evs P', ~ pstep_at [] cfg ef_root (ef_P2 3 0x800) evs (PNext P')).
Proof.
  intros cfg.
  apply (eventfd_setfl_change_refused [] cfg (ef_P2 3 0x800) (ef_root_at 3 0x800)
           (Z_to_bv 64 25));
    vm_compute; first [reflexivity | lia].
Qed.

(** fcntl(4, F_SETFL, 0): fd 4 has the bit, so the call would clear it:
    refused the same way. *)
Theorem procs_eventfd_setfl_clear_refused : forall cfg,
  pstep_at [] cfg ef_root (ef_P2 4 0) [] PError
  /\ (forall evs P', ~ pstep_at [] cfg ef_root (ef_P2 4 0) evs (PNext P')).
Proof.
  intros cfg.
  apply (eventfd_setfl_change_refused [] cfg (ef_P2 4 0) (ef_root_at 4 0)
           (Z_to_bv 64 25));
    vm_compute; first [reflexivity | lia].
Qed.

(* =========================================================================
   Control: the bit kept, while the child lives
   ========================================================================= *)

Definition ef_keep_c : config := pe_cfg ef_shared (ef_root_at 4 0x800).

(** fcntl(4, F_SETFL, O_NONBLOCK): a2 has the bit and so does fd 4.  The
    gate stays shut and the core takes the released step. *)
Theorem procs_eventfd_setfl_keep_answered : forall cfg,
  pstep_at [] cfg ef_root (ef_P2 4 0x800) []
    (PNext (absorb (ef_P2 4 0x800) (ef_root_at 4 0x800) (ef_next ef_keep_c))).
Proof.
  intros cfg.
  apply pstep_other with (e := ef_root_at 4 0x800) (c' := ef_next ef_keep_c).
  2: apply ef_sstep; vm_compute; reflexivity.
  all: vm_compute; reflexivity.
Qed.

(** The answer is 0, and fd 4 still holds the bit in the root's entry. *)
Example procs_eventfd_setfl_keep_result :
  option_map (fun e => (ms_gpr (pe_ms e) 0, fd_lookup (m_fds (pe_model e)) (Z_to_bv 64 4)))
    (look (absorb (ef_P2 4 0x800) (ef_root_at 4 0x800) (ef_next ef_keep_c)) ef_root)
  = Some (Z_to_bv 64 0, Some (FdOpaque (OEventFd (Z_to_bv 64 0x800)))).
Proof. check_eq. Qed.

(* =========================================================================
   Control: the same change with the root alone
   ========================================================================= *)

Definition ef_alone_c : config := pe_cfg ef_shared (ef_root_at 3 0x800).

(** fcntl(3, F_SETFL, O_NONBLOCK) by the same entry, with no other entry
    in the table: the gate stays shut and the call is answered. *)
Theorem procs_eventfd_setfl_alone_answered : forall cfg,
  pstep_at [] cfg ef_root (ef_P1 3 0x800) []
    (PNext (absorb (ef_P1 3 0x800) (ef_root_at 3 0x800) (ef_next ef_alone_c))).
Proof.
  intros cfg.
  apply pstep_other with (e := ef_root_at 3 0x800) (c' := ef_next ef_alone_c).
  2: apply ef_sstep; vm_compute; reflexivity.
  all: vm_compute; reflexivity.
Qed.

(** The answer is 0, and fd 3 now holds the bit. *)
Example procs_eventfd_setfl_alone_result :
  option_map (fun e => (ms_gpr (pe_ms e) 0, fd_lookup (m_fds (pe_model e)) (Z_to_bv 64 3)))
    (look (absorb (ef_P1 3 0x800) (ef_root_at 3 0x800) (ef_next ef_alone_c)) ef_root)
  = Some (Z_to_bv 64 0, Some (FdOpaque (OEventFd (Z_to_bv 64 0x800)))).
Proof. check_eq. Qed.
