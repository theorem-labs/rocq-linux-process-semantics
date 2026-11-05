(** * LinuxProcessSem.Checks.Sys.Kernel.Exit — the exit (93), exit_group (94), wait4 (260) checkers, and their proofs

    Mirrors [Sys/Kernel/Exit.v], which answers to Linux [kernel/exit.c]:
    this file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude.

Definition check_exit (code : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_ret_only eff (Z_to_bv 64 0)
    (with_halted (bv_and code (Z_to_bv 64 255)) m) [].

(** set_tid_address: no writes; the first call records a positive tid
    below the model's [PID_MAX_ENVELOPE] in [m_tid], and every later call
    must return the pinned value (see [Fork.set_tid_address_spec]). *)

Lemma check_exit_sound_ok : forall code eff m m' evs i,
  check_exit code eff m = CheckOk m' evs -> exit_spec code i m (Ok eff m' evs).
Proof.
  intros code eff m m' evs i H.
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  unfold exit_spec.
  eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_exit_sound_unmodeled : forall code eff m i,
  check_exit code eff m = CheckUnmodeled -> exit_spec code i m Unmodeled.
Proof.
  intros code eff m i H. now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_exit_complete_ok : forall code eff m m' evs i,
  exit_spec code i m (Ok eff m' evs) -> check_exit code eff m = CheckOk m' evs.
Proof.
  intros code eff m m' evs i H.
  unfold exit_spec in H. unfold check_exit. sys_unfold.
  cbv iota in H. inv_ok.
  cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma check_exit_complete_unmodeled : forall code m i eff,
  exit_spec code i m Unmodeled -> check_exit code eff m = CheckUnmodeled.
Proof.
  intros code m i eff H.
  unfold exit_spec in H. sys_unfold. cbv iota in H. inv_ok; discriminate.
Qed.

(* ------------------------------------------------- set_tid_address *)


(* ----------------------------------------------------------------- wait4 *)

(** The store a reap's effect may carry, read off the effect: nothing
    when [stat_addr] is NULL, and otherwise exactly one write of four
    bytes at [stat_addr] whose little-endian value [z] is a status word
    [Exit.wait_status_okz] admits.  The last conjunct asks that the bytes
    ARE [Z_to_le_bytes 4 z], so the soundness proof reads the store off
    [Fs.path_eqb_eq] instead of re-deriving the byte encoding. *)
Definition check_wait4_store (stat_addr : word) (ws : list (word * list byte))
    : bool :=
  if w_is0 stat_addr then
    match ws with
    | [] => true
    | _ :: _ => false
    end
  else
    match ws with
    | [(a, bs)] =>
        let z := bytes_le_to_Z bs in
        bv_eqb a stat_addr && Nat.eqb (length bs) 4 && wait_status_okz z
        && path_eqb bs (Z_to_le_bytes 4 z)
    | _ => false
    end.

(** wait4: three argument guards, then the three callers of
    [Exit.wait4_spec].  A caller with no child admits -ECHILD and
    nothing else; [stat_addr] is not read there, because
    [kernel_wait4]'s copy-out is guarded on [ret > 0].  A caller with a
    recorded child declines when the list is empty, when the install bit
    [State.m_sigchld_dfl] is clear (no SIG_DFL install for SIGCHLD made
    while the process had no recorded child), or
    when [stat_addr] is not NULL and not four writable bytes, and
    otherwise admits 0 with
    no write and the model unchanged, or a recorded nonzero pid with the
    store [check_wait4_store] reads, the pid removed from the list.  The
    return decides which: 0 is the bare answer, any other word a reap. *)
Definition check_wait4 (i : SyscallInput) (upid stat_addr options rusage : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (Z.eqb (bv_unsigned upid) WAIT_ANY32) then CheckUnmodeled
  else if negb (Z.eqb (bv_unsigned options) WNOHANG) then CheckUnmodeled
  else if negb (w_is0 rusage) then CheckUnmodeled
  else if m_has_children m then
    match m_child_pids m with
    | [] => CheckUnmodeled
    | _ :: _ =>
        if negb (m_sigchld_dfl m) then CheckUnmodeled
        else if negb (wait4_stat_ok_b (in_wmem i) stat_addr) then CheckUnmodeled
        else
          match eff with
          | mkEffectU r ws [] [] [] [] =>
              if w_is0 r then
                match ws with
                | [] => CheckOk m []
                | _ :: _ => CheckReject
                end
              else if pid_recorded_b r (m_child_pids m)
                      && (clone_pid_ok_b m r && check_wait4_store stat_addr ws)
              then CheckOk (with_child_pids (remove_pid r (m_child_pids m)) m) []
              else CheckReject
          | _ => CheckReject
          end
    end
  else
    match eff with
    | mkEffectU r [] [] [] [] [] =>
        if bv_eqb r (errno_ret ECHILD) then CheckOk m [] else CheckReject
    | _ => CheckReject
    end.

(** Every effect field but the return must be empty: a -ECHILD moves no
    memory.  Five [destruct]s, one per ledger, each closing its cons
    case on the checker's catch-all. *)
Ltac wait4_empty_ledgers ws zs us cs ins tac :=
  destruct ws as [|? ?]; [|tac];
  destruct zs as [|? ?]; [|tac];
  destruct us as [|? ?]; [|tac];
  destruct cs as [|? ?]; [|tac];
  destruct ins as [|? ?]; [|tac].

(** A status word [Exit.wait_status_okz] admits is below 2^16, so its
    four little-endian bytes decode back to it. *)
Lemma wait_status_okz_le_bytes : forall s,
  wait_status_okz s = true -> bytes_le_to_Z (Z_to_le_bytes 4 s) = s.
Proof.
  intros s Hs. unfold wait_status_okz in Hs.
  apply andb_true_iff in Hs as [H0 Hs]. apply Z.leb_le in H0.
  rewrite bytes_le_to_Z_of_le_bytes by exact H0.
  apply Z.mod_small. split; [exact H0|].
  change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z.
  apply orb_true_iff in Hs as [Hs | Hs];
    apply andb_true_iff in Hs as [_ Hs]; apply Z.ltb_lt in Hs; lia.
Qed.

(** What [check_wait4_store] accepts is exactly a store
    [Exit.wait4_spec] makes, for some admitted status word. *)
Lemma check_wait4_store_sound : forall stat_addr ws,
  check_wait4_store stat_addr ws = true ->
  exists s, wait_status_okz s = true /\ ws = wait4_stat_store stat_addr s.
Proof.
  intros stat_addr ws H. unfold check_wait4_store in H. unfold wait4_stat_store.
  destruct (w_is0 stat_addr).
  - destruct ws as [|? ?]; [|discriminate H].
    exists 0%Z. split; reflexivity.
  - destruct ws as [|[a bs] [|? ?]]; try discriminate H.
    cbv beta iota zeta in H.
    apply andb_true_iff in H as [H Hp]. apply andb_true_iff in H as [H Hs].
    apply andb_true_iff in H as [Ha _].
    apply bv_eqb_eq in Ha. apply path_eqb_eq in Hp. subst a.
    exists (bytes_le_to_Z bs). split; [exact Hs|].
    rewrite <- Hp. reflexivity.
Qed.

Lemma check_wait4_store_complete : forall stat_addr s,
  wait_status_okz s = true ->
  check_wait4_store stat_addr (wait4_stat_store stat_addr s) = true.
Proof.
  intros stat_addr s Hs. unfold check_wait4_store, wait4_stat_store.
  destruct (w_is0 stat_addr); [reflexivity|].
  cbv beta iota zeta. rewrite (wait_status_okz_le_bytes s Hs).
  rewrite bv_eqb_refl, length_Z_to_le_bytes, Hs, path_eqb_refl.
  reflexivity.
Qed.

(** A recorded pid is removed: the list loses exactly one entry.  So a
    reap never leaves the model it started from. *)
Lemma remove_pid_length : forall q l,
  pid_recorded_b q l = true -> S (length (remove_pid q l)) = length l.
Proof.
  intros q l. unfold pid_recorded_b.
  induction l as [|p l IH]; intros H; cbn [existsb] in H; [discriminate H|].
  cbn [remove_pid]. destruct (bv_eqb q p) eqn:E.
  - reflexivity.
  - exact (f_equal S (IH H)).
Qed.

(** Every pid the reap admits is nonzero, independently of the raw list. *)
Lemma wait4_pid_nonzero : forall m q,
  clone_pid_ok_b m q = true -> w_is0 q = false.
Proof.
  intros m q H. unfold w_is0.
  destruct (bv_eqb q (Z_to_bv 64 0)) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. subst q.
  unfold clone_pid_ok_b in H. vm_compute in H. discriminate H.
Qed.

Lemma check_wait4_sound_ok : forall i upid stat_addr options rusage eff m m' evs,
  check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs ->
  wait4_spec upid stat_addr options rusage i m (Ok eff m' evs).
Proof.
  intros i upid stat_addr options rusage [ret ws zs us cs ins] m m' evs H.
  unfold check_wait4 in H. unfold wait4_spec.
  destruct (negb (Z.eqb (bv_unsigned upid) WAIT_ANY32)); [discriminate|].
  destruct (negb (Z.eqb (bv_unsigned options) WNOHANG)); [discriminate|].
  destruct (negb (w_is0 rusage)); [discriminate|].
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (m_has_children m) eqn:Hc; cbv iota in H |- *.
  - (* a caller with a child: 0, or a reap *)
    destruct (m_child_pids m) as [|q0 l0] eqn:Hl; cbv iota in H |- *;
      [discriminate|].
    destruct (negb (m_sigchld_dfl m)); cbv iota in H |- *; [discriminate|].
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    destruct (negb (wait4_stat_ok_b (in_wmem i) stat_addr)); cbv iota in H |- *;
      [discriminate|].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct ins as [|? ?]; [|discriminate].
    cbv iota in H.
    destruct (w_is0 ret) eqn:H0; cbv iota in H.
    + (* the bare 0 *)
      destruct ws as [|? ?]; cbv iota in H; [|discriminate].
      injection H as <- <-.
      unfold w_is0 in H0. apply bv_eqb_eq in H0. subst ret.
      apply alt_l. unfold ret_only. apply pure_ok.
    + (* a reap of a recorded pid *)
      destruct (pid_recorded_b ret (q0 :: l0)
                && (clone_pid_ok_b m ret && check_wait4_store stat_addr ws))
        eqn:Hr; cbv iota in H; [|discriminate].
      apply andb_true_iff in Hr as [Hq Hr].
      apply andb_true_iff in Hr as [Hp Hw].
      apply check_wait4_store_sound in Hw as (s & Hs & ->).
      injection H as <- <-.
      apply alt_r.
      eapply bind_ok0;
        [apply (choose_ok _ ret); cbv beta; rewrite Hq, Hp; reflexivity|].
      eapply bind_ok0; [apply (choose_ok _ s); exact Hs|].
      eapply bind_ok0; [apply modify_ok|].
      apply pure_ok.
  - (* no child: -ECHILD *)
    wait4_empty_ledgers ws zs us cs ins discriminate.
    destruct (bv_eqb ret (errno_ret ECHILD)) eqn:Hr; [|discriminate].
    apply bv_eqb_eq in Hr. subst ret.
    inversion H; clear H; subst.
    unfold err_ret, ret_only. apply pure_ok.
Qed.

Lemma check_wait4_sound_unmodeled :
  forall i upid stat_addr options rusage eff m,
  check_wait4 i upid stat_addr options rusage eff m = CheckUnmodeled ->
  wait4_spec upid stat_addr options rusage i m Unmodeled.
Proof.
  intros i upid stat_addr options rusage [ret ws zs us cs ins] m H.
  unfold check_wait4 in H. unfold wait4_spec.
  destruct (negb (Z.eqb (bv_unsigned upid) WAIT_ANY32)); [apply unmodeled_intro|].
  destruct (negb (Z.eqb (bv_unsigned options) WNOHANG)); [apply unmodeled_intro|].
  destruct (negb (w_is0 rusage)); [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (m_has_children m) eqn:Hc; cbv iota in H |- *.
  - destruct (m_child_pids m) as [|q0 l0] eqn:Hl; cbv iota in H |- *;
      [apply unmodeled_intro|].
    destruct (negb (m_sigchld_dfl m)); cbv iota in H |- *;
      [apply unmodeled_intro|].
    eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    destruct (negb (wait4_stat_ok_b (in_wmem i) stat_addr)); cbv iota in H |- *;
      [apply unmodeled_intro|].
    exfalso.
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct ins as [|? ?]; [|discriminate].
    cbv iota in H.
    destruct (w_is0 ret); cbv iota in H; [destruct ws; discriminate|].
    destruct (pid_recorded_b ret (q0 :: l0)
              && (clone_pid_ok_b m ret && check_wait4_store stat_addr ws));
      discriminate.
  - exfalso. wait4_empty_ledgers ws zs us cs ins discriminate.
    destruct (bv_eqb ret (errno_ret ECHILD)); discriminate.
Qed.

Lemma check_wait4_complete_ok :
  forall i upid stat_addr options rusage eff m m' evs,
  wait4_spec upid stat_addr options rusage i m (Ok eff m' evs) ->
  check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs.
Proof.
  intros i upid stat_addr options rusage eff m m' evs H.
  unfold wait4_spec in H. unfold check_wait4.
  destruct (negb (Z.eqb (bv_unsigned upid) WAIT_ANY32));
    [sys_unfold; inv_ok|].
  destruct (negb (Z.eqb (bv_unsigned options) WNOHANG)); [sys_unfold; inv_ok|].
  destruct (negb (w_is0 rusage)); [sys_unfold; inv_ok|].
  sys_unfold. inv_ok.
  match goal with
  | |- context [m_has_children ?mm] => destruct (m_has_children mm) eqn:Hc
  end; hall Hc; inv_ok.
  - (* a caller with a child: one goal per admitted answer *)
    match goal with
    | |- context [m_child_pids ?mm] =>
        destruct (m_child_pids mm) as [|q0 l0] eqn:Hl
    end; hall Hl; inv_ok.
    match goal with
    | |- context [m_sigchld_dfl ?mm] =>
        destruct (negb (m_sigchld_dfl mm)) eqn:Hd
    end; hall Hd; inv_ok.
    match goal with
    | |- context [wait4_stat_ok_b ?w ?a] =>
        destruct (negb (wait4_stat_ok_b w a)) eqn:Hw
    end; hall Hw; inv_ok.
    all: cbv beta iota.
    (* the bare 0 *)
    all: try (unfold w_is0; rewrite bv_eqb_refl; reflexivity).
    (* a reap *)
    all: match goal with
         | Hq : andb (pid_recorded_b ?q _) (clone_pid_ok_b ?mm ?q) = true,
           Hs : wait_status_okz ?s = true |- _ =>
             apply andb_true_iff in Hq as [Hq Hp];
             pose proof (wait4_pid_nonzero mm q Hp) as Hn;
             rewrite Hn, Hq, Hp, (check_wait4_store_complete stat_addr s Hs);
             reflexivity
         end.
  - (* no child: -ECHILD *)
    cbv beta iota. rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma check_wait4_complete_unmodeled :
  forall i upid stat_addr options rusage m eff,
  wait4_spec upid stat_addr options rusage i m Unmodeled ->
  check_wait4 i upid stat_addr options rusage eff m = CheckUnmodeled.
Proof.
  intros i upid stat_addr options rusage m eff H.
  unfold wait4_spec in H. unfold check_wait4.
  destruct (negb (Z.eqb (bv_unsigned upid) WAIT_ANY32)); [reflexivity|].
  destruct (negb (Z.eqb (bv_unsigned options) WNOHANG)); [reflexivity|].
  destruct (negb (w_is0 rusage)); [reflexivity|].
  (* -ECHILD, 0 and a reap all answer, so [Unmodeled] comes only from
     the empty list, the missing SIGCHLD install or the unwritable
     [stat_addr], where the checker declines too *)
  sys_unfold. inv_ok.
  destruct (m_has_children m) eqn:Hc; hall Hc; inv_ok;
    destruct (m_child_pids m) as [|q0 l0] eqn:Hl; hall Hl; inv_ok;
    try reflexivity;
    destruct (negb (m_sigchld_dfl m)) eqn:Hd; hall Hd; inv_ok;
    try reflexivity;
    destruct (negb (wait4_stat_ok_b (in_wmem i) stat_addr)) eqn:Hw; hall Hw;
    inv_ok; reflexivity.
Qed.
