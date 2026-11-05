(** * LinuxProcessSem.Checks.Cases.Kernel.ProcsWait4Sigchld — wait4 (260) in the multi-process core, by SIGCHLD disposition

    Not part of the trusted specification: this file is QA on the
    definitions, in the sense of [Checks.Examples]'s header.

    THE FIXTURE.  [Checks.Cases.Kernel.ProcsKill]'s two-entry table: the
    root has key 1 and the child key 2, the root its parent.  The child
    has exited with code 7 ([State.with_halted]), so it is a zombie of the
    table.  The root is at wait4(-1, &st, WNOHANG, NULL), [st] four
    writable bytes at 0x1000.  The root's model has [State.procst_sigchld_dfl]
    written by hand ([State.with_sigchld_dfl]) over the fixture's launch
    model: set, as at a SIG_DFL launch or after the SIGCHLD SIG_DFL
    install [Kernel.Signal.sigchld_dfl_install] answers; or clear, as at
    a SIG_IGN launch ([State.in_sigchld_default] false) with no install.

    THE POSITIVE CASE (SIG_DFL): the core reaps the child, as before the
    gate read the bit: the root's a0 is the child's pid 2 and the child's
    entry is gone ([Procs.pstep_wait_nohang_reap]).

    THE DECLINE (no SIG_DFL install, as under a launcher's SIG_IGN, where
    Linux's [do_notify_parent] reaps the child at its exit;
    kernel/signal.c:2241-2261, v6.18.46): the same call is refused
    ([Procs.pstep_wait_refuse]) and every step of the root is the refusal
    ([Checks.ProcsSigchld.sigchld_clear_wait4_declines]), so no status is
    answered.  The blocking wait4(-1, &st, 0, NULL) of that root gets no
    answer either.

    THE LIVE CHILD (no SIG_DFL install, the child still running): WNOHANG
    answers 0 ([Procs.pstep_wait_nohang_zero]), as Linux does under either
    disposition: [wait_consider_task] clears [notask_error] for a live
    child and [__do_wait] returns it under WNOHANG (kernel/exit.c,
    lines 1534-1539 and 1704-1709, v6.18.46). *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext.
From LinuxProcessSemantics.LinuxProcessSem Require Import Procs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ProcsWait4Gate ProcsSigchld.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel Require Import ProcsKill.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The fixture
   ========================================================================= *)

(** [st]: one writable page at 0x1000. *)
Definition sw_stat : word := Z_to_bv 64 0x1000.

Definition sw_mem : word -> option byte :=
  fun a => if Z.eqb (bv_unsigned a / 4096) 1 then Some (Z_to_bv 8 0) else None.

(** The machine at a [wait4] ecall: 260 pending, a0 = -1 (any child),
    a1 = [st], a2 = the option word, a3 = NULL. *)
Definition sw_wait_ms (opts : Z) : machine_state :=
  let base := {| ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
                 ms_pc_val := Z_to_bv 64 0x100;
                 ms_svc_pending := Some (Z_to_bv 64 260);
                 ms_resv := None; ms_fcsr := Z_to_bv 32 0;
                 ms_mem := sw_mem; ms_rom := fun _ => None |} in
  set_reg (set_reg (set_reg (set_reg base (Z_to_bv 5 10) (Z_to_bv 64 (-1)))
                            (Z_to_bv 5 11) sw_stat)
                   (Z_to_bv 5 12) (Z_to_bv 64 opts))
          (Z_to_bv 5 13) (Z_to_bv 64 0).

(** The root's model with the install bit written by hand. *)
Definition sw_root_entry (dfl : bool) (opts : Z) : ProcessEntry :=
  mkEntry pk_root None (sw_wait_ms opts)
    (clear_shared (with_sigchld_dfl dfl pk_base)) [] init_nsctx.

(** The child, exited with code 7. *)
Definition sw_child_entry : ProcessEntry :=
  mkEntry pk_child (Some pk_root) pk_idle_ms
    (clear_shared (with_halted (Z_to_bv 64 7) pk_base)) [] init_nsctx.

Definition sw_P (dfl : bool) (opts : Z) : pconfig :=
  mkPCfg [(pk_root, sw_root_entry dfl opts); (pk_child, sw_child_entry)] pk_root pk_shared.

(** The fixture's launch model is a SIG_DFL launch ([mkProcInput]'s default
    for [State.in_sigchld_default]), so the clear bit below is the
    hand-written one: a SIG_IGN launch, not this fixture's own. *)
Example sw_base_bit_dfl : m_sigchld_dfl pk_base = true.
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   SIG_DFL: the answer the core gave before it read the bit
   ========================================================================= *)

Definition sw_status : word :=
  bv_mul (bv_and (Z_to_bv 64 7) (Z_to_bv 64 255)) (Z_to_bv 64 256).

Definition sw_eff : SyscallEffect :=
  mkEffect pk_child (wait4_nohang_writes sw_stat sw_status (Z_to_bv 64 0) some_rusage) [].

Definition sw_model'' : Model :=
  match materialize_model_accesses
          (cfg_model (pe_cfg pk_shared (sw_root_entry true WNOHANG)))
          (syscall_effect_accesses sw_eff) with
  | Some m => m
  | None => pk_base
  end.

Definition sw_reaped : pconfig :=
  wait4_reap_result (sw_P true WNOHANG) (sw_root_entry true WNOHANG) pk_child sw_eff sw_model''.

Theorem sw_dfl_reaps : forall cfg,
  pstep_at [] cfg pk_root (sw_P true WNOHANG) [] (PNext sw_reaped).
Proof.
  intros cfg.
  apply (pstep_wait_nohang_reap [] cfg (sw_P true WNOHANG) (sw_root_entry true WNOHANG)
           pk_child sw_child_entry (Z_to_bv 64 260) sw_stat (Z_to_bv 64 0) some_rusage
           sw_status sw_eff sw_model'' false).
  all: first
    [ vm_compute; reflexivity
    | intros Hc; vm_compute in Hc; discriminate Hc
    | intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate Hc ].
Qed.

(** The answer: the child's pid in a0, the status 7 << 8, and the child's
    entry gone. *)
Example sw_dfl_answer :
  option_map (fun e => bv_unsigned (ms_gpr (pe_ms e) 0)) (look sw_reaped pk_root) = Some 2%Z
  /\ look sw_reaped pk_child = None
  /\ bv_unsigned sw_status = 1792%Z.
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(* =========================================================================
   No SIG_DFL install: the decline
   ========================================================================= *)

(** The same call is refused ... *)
Theorem sw_ign_refused : forall cfg,
  pstep_at [] cfg pk_root (sw_P false WNOHANG) [] PError.
Proof.
  intros cfg.
  apply (pstep_wait_refuse [] cfg (sw_P false WNOHANG) (sw_root_entry false WNOHANG));
    vm_compute; reflexivity.
Qed.

(** ... and it is the only thing the root's step can be: no reap, no
    zero, no status. *)
Theorem sw_ign_declines : forall cfg evs r,
  pstep_at [] cfg pk_root (sw_P false WNOHANG) evs r -> r = PError.
Proof.
  intros cfg evs r H.
  apply (sigchld_clear_wait4_declines [] cfg pk_root (sw_P false WNOHANG)
           (sw_root_entry false WNOHANG) evs r);
    [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity
    | exact H ].
Qed.

(** The blocking shape of the same root: no answer either. *)
Theorem sw_ign_blocking_declines : forall cfg evs r,
  pstep_at [] cfg pk_root (sw_P false 0) evs r -> r = PError.
Proof.
  intros cfg evs r H.
  apply (sigchld_clear_wait4_declines [] cfg pk_root (sw_P false 0)
           (sw_root_entry false 0) evs r);
    [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity
    | exact H ].
Qed.

(* =========================================================================
   No SIG_DFL install, a live child: WNOHANG answers 0
   ========================================================================= *)

(** The child, still running at an instruction. *)
Definition sw_live_child_entry : ProcessEntry :=
  mkEntry pk_child (Some pk_root) pk_idle_ms (clear_shared pk_base) [] init_nsctx.

Definition sw_P_live : pconfig :=
  mkPCfg [(pk_root, sw_root_entry false WNOHANG); (pk_child, sw_live_child_entry)]
    pk_root pk_shared.

Definition sw_zeroed : pconfig := wait4_zero_result sw_P_live (sw_root_entry false WNOHANG).

(** Not refused ... *)
Example sw_ign_live_not_refused :
  wait4_refused_b [] sw_P_live (sw_root_entry false WNOHANG) = false.
Proof. vm_compute. reflexivity. Qed.

(** ... but answered 0, the bit clear. *)
Theorem sw_ign_live_zero : forall cfg,
  pstep_at [] cfg pk_root sw_P_live [] (PNext sw_zeroed).
Proof.
  intros cfg.
  apply (pstep_wait_nohang_zero [] cfg sw_P_live (sw_root_entry false WNOHANG)
           (Z_to_bv 64 260) sw_stat (Z_to_bv 64 0));
    vm_compute; reflexivity.
Qed.

Example sw_ign_live_answer :
  option_map (fun e => bv_unsigned (ms_gpr (pe_ms e) 0)) (look sw_zeroed pk_root) = Some 0%Z
  /\ m_sigchld_dfl (pe_model (sw_root_entry false WNOHANG)) = false.
Proof. split; vm_compute; reflexivity. Qed.
