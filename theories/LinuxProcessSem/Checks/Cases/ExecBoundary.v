(** * LinuxProcessSem.Checks.Cases.ExecBoundary — the path-argument launch and the execve boundary

    Worked examples for three additions to [Run]: the second launch
    predicate [Run.valid_input_paths], which admits arguments that
    contain "/"; [Run.execve_boundary], the configuration at which a
    launcher's run ends in an [execve] the model does not follow; and
    [Run.star_calls], the log of the calls a run made.  Each comes as a
    PAIR: the case the ordinary vocabulary refuses or cannot state, and a
    control on which the old and the new vocabulary agree. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Examples.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
Import ListNotations.
Open Scope bv_scope.

(** Two distinct bytes are different: compare their values. *)
Local Ltac bv_neq H :=
  apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H.
Local Ltac bv_neq_goal := let H := fresh "H" in intros H; bv_neq H.

(** [~ In b l] for a literal list [l] none of whose bytes is [b]. *)
Local Ltac not_in :=
  let H := fresh "H" in
  intros H; cbn in H;
  repeat (destruct H as [H|H]; [bv_neq H|]); exact H.

(* =========================================================================
   The path-argument launch
   ========================================================================= *)

(** "/tmp", an example argument that holds a separator. *)
Definition slash_tmp : list byte :=
  [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112].

(** "tmp", the same word without its separator. *)
Definition plain_tmp : list byte :=
  [Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112].

(** The bounds both argv predicates share, for a two-word argv whose
    first word is empty: discharged once, by computation. *)
Local Ltac argv_bounds :=
  repeat split;
  try (vm_compute; intros Hc; discriminate Hc);
  repeat constructor;
  try (vm_compute; intros Hc; discriminate Hc);
  try not_in.

(** THE CASE: an argv whose second word is a path is no launch at all
    under [Run.valid_argv] ... *)
Example slash_argv_refused : ~ valid_argv [[]; slash_tmp].
Proof.
  intros (_ & _ & _ & _ & H). inversion H as [|x l Hx _]; subst.
  destruct Hx as [Hs _]. vm_compute in Hs. discriminate Hs.
Qed.

(** ... and is one under [Run.valid_argv_paths]. *)
Example slash_argv_admitted : valid_argv_paths [[]; slash_tmp].
Proof. unfold valid_argv_paths. argv_bounds. Qed.

(** THE CONTROL: an argv with no separator is admitted by both. *)
Example plain_argv_both :
  valid_argv [[]; plain_tmp] /\ valid_argv_paths [[]; plain_tmp].
Proof.
  assert (H : valid_argv [[]; plain_tmp]).
  { unfold valid_argv. argv_bounds; vm_compute; reflexivity. }
  split; [exact H | apply valid_argv_paths_of_valid_argv, H].
Qed.

(** The demo input of [Checks.Examples] with "/tmp" as its second
    argument: a whole valid launch under the new predicate, read off
    [Checks.Examples.demo_input_valid] clause by clause.  The two inputs
    differ in argv alone, so only the argv clause is discharged afresh;
    each other clause is the demo's, up to conversion, or (for
    [Run.valid_launch], whose byte count reads argv) by computation. *)
Definition paths_demo_input : ProcInput :=
  mkProcInput [[]; slash_tmp] [] [] IEof demo_uid demo_gid demo_groups
              net_silent default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

Example paths_demo_input_valid : valid_input_paths paths_demo_input.
Proof.
  pose proof demo_input_valid as H. red in H |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  split; [exact slash_argv_admitted|].
  repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | match goal with Hl : valid_launch _ |- valid_launch _ =>
              destruct Hl as [He _]; split;
              [exact He | vm_compute; intros Hc; discriminate Hc]
            end ].
Qed.

Example paths_demo_input_not_ordinary : ~ valid_input paths_demo_input.
Proof.
  intros H. red in H. destruct H as [Ha _]. exact (slash_argv_refused Ha).
Qed.

(* =========================================================================
   The execve boundary
   ========================================================================= *)

(** A memory holding [bs] from address [base] on, and nothing else. *)
Definition bytes_mem (base : Z) (bs : list byte) : word -> option byte :=
  fun a => let off := (bv_unsigned a - base)%Z in
           if ((0 <=? off) && (off <? Z.of_nat (length bs)))%Z
           then Some (nth (Z.to_nat off) bs (Z_to_bv 8 0)) else None.

Definition mem_union (m1 m2 : word -> option byte) : word -> option byte :=
  fun a => match m1 a with Some b => Some b | None => m2 a end.

(** The 8 little-endian bytes of [z]. *)
Definition le8 (z : Z) : list byte :=
  map (fun k => Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))) (seq 0 8).

(** The launcher's last call: execve("/b", ["/b"; "/tmp"], {NULL}).
    The path string sits at 0x1000, "/tmp" at 0x1010, the argv array at
    0x2000 and the empty envp array (one NULL word) at 0x3000. *)
Definition xb_path : list byte := [Z_to_bv 8 47; Z_to_bv 8 98].
Definition xb_mem : word -> option byte :=
  mem_union (bytes_mem 0x1000 (xb_path ++ [Z_to_bv 8 0]))
  (mem_union (bytes_mem 0x1010 (slash_tmp ++ [Z_to_bv 8 0]))
  (mem_union (bytes_mem 0x2000 (le8 0x1000 ++ le8 0x1010 ++ le8 0))
             (bytes_mem 0x3000 (le8 0)))).

(** The machine at the [ecall]: a0..a2 hold the three pointers and the
    pending number is [n]. *)
Definition xb_ms (n : Z) : machine_state :=
  let base := {| ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
                 ms_pc_val := Z_to_bv 64 0x10000;
                 ms_svc_pending := Some (Z_to_bv 64 n);
                 ms_resv := None; ms_fcsr := Z_to_bv 32 0;
                 ms_mem := xb_mem; ms_rom := fun _ => None |} in
  set_reg (set_reg (set_reg base (Z_to_bv 5 10) (Z_to_bv 64 0x1000))
                   (Z_to_bv 5 11) (Z_to_bv 64 0x2000))
          (Z_to_bv 5 12) (Z_to_bv 64 0x3000).

Definition xb_model : Model :=
  init_model [] (Z_to_bv 64 0) (Z_to_bv 64 0) demo_sp demo_limit (demo_input [] IEof).

Definition xb_cfg (n : Z) : config := mkCfg (xb_ms n) xb_model.

(** One pointer of an argv or envp array, at a computed address. *)
Local Ltac word_at_le8 z :=
  exists (le8 z); split; [reflexivity|]; split; [|check_eq];
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try lia; check_eq.

(** A C string of at most four bytes at a computed address. *)
Local Ltac cstr_at_lit :=
  split; [not_in|];
  split; [let j := fresh "j" in let Hj := fresh "Hj" in
          intros j Hj; cbn in Hj;
          destruct j as [|[|[|[|j]]]]; try lia; check_eq
         | check_eq].

(** THE CASE: the configuration is at the boundary, with the path, the
    argv and the empty envp it passes. *)
Example xb_at_boundary :
  execve_boundary (xb_cfg 221) xb_path [xb_path; slash_tmp] [].
Proof.
  unfold execve_boundary, xb_cfg. cbn [cfg_ms cfg_model].
  split; [vm_compute; reflexivity|]. split; [reflexivity|].
  split; [|split].
  - cstr_at_lit.
  - split.
    + intros k Hk; cbn in Hk.
      destruct k as [|[|k]]; [| |lia].
      * exists (Z_to_bv 64 0x1000).
        split; [word_at_le8 (0x1000%Z)|]. split; [bv_neq_goal|].
        cstr_at_lit.
      * exists (Z_to_bv 64 0x1010).
        split; [word_at_le8 (0x1010%Z)|]. split; [bv_neq_goal|].
        cstr_at_lit.
    + word_at_le8 (0%Z).
  - split; [intros k Hk; cbn in Hk; lia|]. word_at_le8 (0%Z).
Qed.

(** And the run stops there: whatever segments the image has, the only
    step is the error of an uncovered call, with no event. *)
Example xb_boundary_stops : forall segs evs s,
  sstep segs (xb_cfg 221) evs s -> evs = [] /\ s = SError.
Proof.
  intros segs evs s Hs.
  exact (execve_boundary_stops segs _ _ _ _ xb_at_boundary evs s Hs).
Qed.

(** THE CONTROL: the same memory and registers at a pending [clone]
    (220) is no exec boundary, for any strings. *)
Example xb_clone_not_boundary : forall p a e,
  ~ execve_boundary (xb_cfg 220) p a e.
Proof.
  intros p a e (_ & Hsvc & _). cbn [cfg_ms xb_cfg] in Hsvc.
  apply (f_equal (fun o => match o with Some w => bv_unsigned w | None => 0%Z end))
    in Hsvc.
  vm_compute in Hsvc. discriminate Hsvc.
Qed.

(* =========================================================================
   The call log ends at the boundary
   ========================================================================= *)

(** From the boundary no call returns and no step is taken: the only
    logged run is the empty one.  This is what lets a statement read
    "the log up to the exec" as the whole log of the launcher. *)
Example xb_log_ends_at_boundary : forall segs tr log c',
  star_calls segs (xb_cfg 221) tr log c' ->
  tr = [] /\ log = [] /\ c' = xb_cfg 221.
Proof.
  intros segs tr log c' H.
  assert (E : ms_svc_pending (xb_ms 221) = Some (Z_to_bv 64 221)) by reflexivity.
  unfold xb_cfg in *. inversion H; subst.
  - repeat split.
  - exfalso.
    match goal with
    | Hsp : syscall_spec _ _ (Ok _ _ _) |- _ =>
        apply syscall_spec_execve_unmodeled in Hsp; [discriminate Hsp|];
        cbn; congruence
    end.
  - exfalso.
    match goal with
    | Hs : sstep _ _ _ (SNext _) |- _ =>
        destruct (execve_boundary_stops segs _ _ _ _ xb_at_boundary _ _ Hs) as [_ Hc];
        discriminate Hc
    end.
Qed.

(* =========================================================================
   The call log records each call that returned
   ========================================================================= *)

(** [xb_ms] with a3..a5 set as well, so that a0..a5 at the [ecall] are
    six distinct words, none of them the uid getuid answers. *)
Definition xb_call_ms (n : Z) : machine_state :=
  set_reg (set_reg (set_reg (xb_ms n) (Z_to_bv 5 13) (Z_to_bv 64 0x4000))
                   (Z_to_bv 5 14) (Z_to_bv 64 0x5000))
          (Z_to_bv 5 15) (Z_to_bv 64 0x6000).

Definition xb_call_cfg (n : Z) : config := mkCfg (xb_call_ms n) xb_model.

(** a0..a5 at the [ecall]. *)
Definition xb_call_args : list word :=
  [Z_to_bv 64 0x1000; Z_to_bv 64 0x2000; Z_to_bv 64 0x3000;
   Z_to_bv 64 0x4000; Z_to_bv 64 0x5000; Z_to_bv 64 0x6000].

Lemma xb_call_args_at : syscall_args (xb_call_ms 174) = xb_call_args.
Proof. check_eq. Qed.

(** getuid's one answer on [xb_model], whose uid is [demo_uid] (1000). *)
Definition xb_getuid_eff : SyscallEffect := mkEffect demo_uid [] [].

(** The configuration after the getuid returns: a0 holds the uid, the
    pc is past the [ecall], and the model is unchanged. *)
Definition xb_getuid_after : config :=
  mkCfg (advance_past_svc (apply_effect (xb_call_ms 174) xb_getuid_eff)) xb_model.

(** The record the log must hold for that call: the number from a7,
    a0..a5 at the [ecall], a0 after the call, and what the call stored:
    nothing, no copy-out and no zero-filled range. *)
Definition xb_getuid_call : SysCall :=
  mkSysCall (Z_to_bv 64 174) xb_call_args demo_uid [] [].

Lemma xb_getuid_spec_ok : forall segs,
  syscall_spec (sys_input segs (xb_call_ms 174) (Z_to_bv 64 174)) xb_model
    (Ok xb_getuid_eff xb_model []).
Proof.
  intros segs. apply check_syscall_sound_ok.
  rewrite check_syscall_getuid by (vm_compute; reflexivity).
  check_eq.
Qed.

Lemma xb_getuid_spec_det : forall segs eff m' evs,
  syscall_spec (sys_input segs (xb_call_ms 174) (Z_to_bv 64 174)) xb_model
    (Ok eff m' evs) ->
  eff = xb_getuid_eff /\ m' = xb_model /\ evs = [].
Proof.
  intros segs eff m' evs H.
  apply check_syscall_complete_ok in H.
  rewrite check_syscall_getuid in H by (vm_compute; reflexivity).
  unfold check_getid in H. apply check_ret_only_ok_iff in H.
  destruct H as (-> & -> & ->). split; [|split; reflexivity].
  check_eq.
Qed.

(** THE CASE: a getuid at [xb_call_cfg 174] returns, and its one-step
    run carries exactly [xb_getuid_call] in its log. *)
Example xb_getuid_logged : forall segs,
  star_calls segs (xb_call_cfg 174) [] [xb_getuid_call] xb_getuid_after.
Proof.
  intros segs.
  replace [xb_getuid_call] with
    [mkSysCall (Z_to_bv 64 174) (syscall_args (xb_call_ms 174))
       (eff_ret xb_getuid_eff) (eff_writes xb_getuid_eff)
       (eff_zeros xb_getuid_eff)] by check_eq.
  change (@nil event) with (@nil event ++ @nil event).
  apply (star_calls_ret segs (xb_call_ms 174) xb_model (Z_to_bv 64 174)
           xb_getuid_eff xb_model xb_model [] [] [] xb_getuid_after).
  - vm_compute. reflexivity.
  - reflexivity.
  - apply xb_getuid_spec_ok.
  - vm_compute. reflexivity.
  - apply materialize_model_accesses_no_lazy. vm_compute. reflexivity.
  - apply star_calls_refl.
Qed.

(** The call is the only step from [xb_call_cfg 174], whatever the
    image: no instruction runs while a call is pending, getuid has one
    answer, and it neither faults, declines nor ends the process. *)
Lemma xb_getuid_only_step : forall segs evs s,
  sstep segs (xb_call_cfg 174) evs s -> evs = [] /\ s = SNext xb_getuid_after.
Proof.
  intros segs evs s Hs. unfold xb_call_cfg in Hs.
  assert (Hsvc : ms_svc_pending (xb_call_ms 174) = Some (Z_to_bv 64 174))
    by reflexivity.
  assert (Hlazy : m_vm_lazy xb_model = []) by (vm_compute; reflexivity).
  assert (Hnh : m_halted xb_model = None) by (vm_compute; reflexivity).
  assert (Hnk : m_killed xb_model = None) by (vm_compute; reflexivity).
  inversion Hs; subst; try congruence.
  all: match goal with
       | H : ms_svc_pending _ = Some ?y |- _ =>
           is_var y; rewrite Hsvc in H; injection H as <-
       end.
  all: first
    [ match goal with
      | Hsp : syscall_spec _ _ Unmodeled |- _ =>
          pose proof (check_syscall_complete_unmodeled _ _ xb_getuid_eff Hsp) as Hc;
          rewrite (check_syscall_complete_ok _ _ _ _ _ (xb_getuid_spec_ok segs)) in Hc;
          discriminate Hc
      end
    | match goal with
      | Hsp : syscall_spec _ _ (Ok _ _ _) |- _ =>
          destruct (xb_getuid_spec_det _ _ _ _ Hsp) as (-> & -> & ->)
      end;
      first
        [ match goal with
          | Hm : materialize_model_accesses _ _ = Some _ |- _ =>
              rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hm;
              injection Hm as <-; split; reflexivity
          end
        | match goal with
          | Hm : materialize_model_accesses _ _ = None |- _ =>
              rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hm;
              discriminate Hm
          end
        | exfalso; congruence ] ].
Qed.

(** THE LOG IS DETERMINED BY THE RUN: every logged run from
    [xb_call_cfg 174] is the empty one, or its log starts with exactly
    [xb_getuid_call].  So no other [sc_ret], and not the registers after
    the call, can stand in the record of that call. *)
Example xb_getuid_log_head : forall segs tr log c',
  star_calls segs (xb_call_cfg 174) tr log c' ->
  (tr = [] /\ log = [] /\ c' = xb_call_cfg 174) \/
  exists rest, log = xb_getuid_call :: rest.
Proof.
  intros segs tr log c' H.
  assert (Hsvc : ms_svc_pending (xb_call_ms 174) = Some (Z_to_bv 64 174))
    by reflexivity.
  unfold xb_call_cfg in H. inversion H; subst.
  - left. repeat split.
  - right.
    match goal with
    | Hp : ms_svc_pending _ = Some ?y |- _ =>
        is_var y; rewrite Hsvc in Hp; injection Hp as <-
    end.
    match goal with
    | Hsp : syscall_spec _ _ (Ok _ _ _) |- _ =>
        destruct (xb_getuid_spec_det _ _ _ _ Hsp) as (-> & _ & _)
    end.
    match goal with |- exists _, _ :: ?l = _ => exists l end.
    rewrite xb_call_args_at. reflexivity.
  - exfalso.
    match goal with
    | Hs : sstep _ _ _ (SNext ?c2), Hor : _ \/ _ |- _ =>
        destruct (xb_getuid_only_step _ _ _ Hs) as [_ Hc2];
        injection Hc2 as ->;
        destruct Hor as [Hn | Hh];
        [ cbn [cfg_ms] in Hn; rewrite Hsvc in Hn; discriminate Hn
        | apply Hh; vm_compute; reflexivity ]
    end.
Qed.

(** Two logs that differ from [xb_getuid_call] in one field: the uid
    answered with 0, and the record read off the registers after the
    call, whose a0 is the uid.  Neither is the log of any run from
    [xb_call_cfg 174]. *)
Example xb_getuid_other_logs_refused : forall segs tr rest c',
  ~ star_calls segs (xb_call_cfg 174) tr
      (mkSysCall (Z_to_bv 64 174) xb_call_args (Z_to_bv 64 0) [] [] :: rest) c' /\
  ~ star_calls segs (xb_call_cfg 174) tr
      (mkSysCall (Z_to_bv 64 174) (syscall_args (cfg_ms xb_getuid_after)) demo_uid
         [] [] :: rest) c'.
Proof.
  intros segs tr rest c'. split; intros H;
    destruct (xb_getuid_log_head _ _ _ _ H) as [(_ & Hl & _) | (r & Hl)];
    [ discriminate Hl
    | apply (f_equal (fun l => bv_unsigned (sc_ret (hd xb_getuid_call l)))) in Hl;
      vm_compute in Hl; discriminate Hl
    | discriminate Hl
    | apply (f_equal (fun l =>
               bv_unsigned (hd (Z_to_bv 64 0) (sc_args (hd xb_getuid_call l)))))
        in Hl;
      vm_compute in Hl; discriminate Hl ].
Qed.

(** THE CONTROL: the same run is a [star] run, which the vocabulary
    before [star_calls] already states. *)
Example xb_getuid_star : forall segs,
  star segs (xb_call_cfg 174) [] xb_getuid_after.
Proof. intros segs. exact (star_calls_star _ _ _ _ _ (xb_getuid_logged segs)). Qed.

(* =========================================================================
   The call log records what a call stored
   ========================================================================= *)

(** capget(header, dataptr) by [xb_model]'s process, whose three uids
    are 1000: version 3 and pid 0 in the header at 0x6000 (the eight
    bytes of [le8] of the version are the version word and a zero pid
    word), and a mapped, writable 24-byte destination at 0x7000. *)
Definition xc_mem : word -> option byte :=
  mem_union (bytes_mem 0x6000 (le8 LINUX_CAPABILITY_VERSION_3))
            (bytes_mem 0x7000 (repeat (Z_to_bv 8 0) 24)).

Definition xc_ms : machine_state :=
  let base := {| ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
                 ms_pc_val := Z_to_bv 64 0x10000;
                 ms_svc_pending := Some (Z_to_bv 64 90);
                 ms_resv := None; ms_fcsr := Z_to_bv 32 0;
                 ms_mem := xc_mem; ms_rom := fun _ => None |} in
  set_reg (set_reg base (Z_to_bv 5 10) (Z_to_bv 64 0x6000))
          (Z_to_bv 5 11) (Z_to_bv 64 0x7000).

Definition xc_cfg : config := mkCfg xc_ms xb_model.

(** a0..a5 at the [ecall]. *)
Definition xc_args : list word :=
  [Z_to_bv 64 0x6000; Z_to_bv 64 0x7000; Z_to_bv 64 0; Z_to_bv 64 0;
   Z_to_bv 64 0; Z_to_bv 64 0].

Lemma xc_args_at : syscall_args xc_ms = xc_args.
Proof. check_eq. Qed.

Definition xc_dst : word := Z_to_bv 64 0x7000.

(** Six zero words: empty effective, permitted and inheritable sets. *)
Definition xc_image : list byte := repeat (Z_to_bv 8 0) 24.

(** One answer: 0, the 24 bytes at the destination, the two header
    reads on the ledger. *)
Definition xc_eff : SyscallEffect :=
  mkEffectU (Z_to_bv 64 0) [(xc_dst, xc_image)] [] [] []
    (cap_header_reads (Z_to_bv 64 0x6000)).

Definition xc_after : config :=
  mkCfg (advance_past_svc (apply_effect xc_ms xc_eff)) xb_model.

(** The record of that answer: number 90, a0..a5, 0, the 24 bytes it
    stored, and no zero-filled range. *)
Definition xc_call : SysCall :=
  mkSysCall (Z_to_bv 64 90) xc_args (Z_to_bv 64 0) [(xc_dst, xc_image)] [].

(** At this configuration every gate of the capget checker passes and
    what is left is the copy-out. *)
Lemma xc_capget_check : forall segs eff,
  check_syscall (sys_input segs xc_ms (Z_to_bv 64 90)) eff xb_model
  = check_capget_copy xc_dst (cap_header_reads (Z_to_bv 64 0x6000)) eff xb_model.
Proof. intros segs eff. vm_compute. reflexivity. Qed.

Lemma xc_spec_ok : forall segs,
  syscall_spec (sys_input segs xc_ms (Z_to_bv 64 90)) xb_model
    (Ok xc_eff xb_model []).
Proof.
  intros segs. apply check_syscall_sound_ok. rewrite xc_capget_check.
  check_eq.
Qed.

(** Every answer at this configuration: 0, one copy-out of an image
    [capget_data_ok] admits at the destination, the header reads, and
    the model unchanged. *)
Lemma xc_spec_inv : forall segs eff m' evs,
  syscall_spec (sys_input segs xc_ms (Z_to_bv 64 90)) xb_model (Ok eff m' evs) ->
  exists bs, eff = mkEffectU (Z_to_bv 64 0) [(xc_dst, bs)] [] [] []
                     (cap_header_reads (Z_to_bv 64 0x6000))
             /\ capget_data_ok bs = true /\ m' = xb_model /\ evs = [].
Proof.
  intros segs eff m' evs H.
  apply check_syscall_complete_ok in H. rewrite xc_capget_check in H.
  unfold check_capget_copy in H.
  destruct eff as [r ws zs us cs cis].
  destruct ws as [|[a bs] [|? ?]]; try discriminate.
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct (bv_eqb r (Z_to_bv 64 0) && bv_eqb a xc_dst && capget_data_ok bs
            && access_ranges_eqb cis (cap_header_reads (Z_to_bv 64 0x6000))) eqn:Hok;
    [|discriminate].
  injection H as Hm Hevs. subst m' evs.
  apply andb_true_iff in Hok as [Hok Hcis].
  apply andb_true_iff in Hok as [Hok Hdata].
  apply andb_true_iff in Hok as [Hr Ha].
  apply bv_eqb_eq in Hr. apply bv_eqb_eq in Ha.
  apply access_ranges_eqb_eq in Hcis. subst r a cis.
  exists bs. split; [reflexivity|]. split; [exact Hdata|]. split; reflexivity.
Qed.

(** No step from [xc_cfg] halts the process: capget returns. *)
Lemma xc_next_not_halted : forall segs evs c2,
  sstep segs xc_cfg evs (SNext c2) -> m_halted (cfg_model c2) = None.
Proof.
  intros segs evs c2 Hs. unfold xc_cfg in Hs.
  assert (Hsvc : ms_svc_pending xc_ms = Some (Z_to_bv 64 90)) by reflexivity.
  assert (Hlazy : m_vm_lazy xb_model = []) by (vm_compute; reflexivity).
  assert (Hnh : m_halted xb_model = None) by (vm_compute; reflexivity).
  assert (Hnk : m_killed xb_model = None) by (vm_compute; reflexivity).
  inversion Hs; subst; try congruence.
  all: match goal with
       | Hp : ms_svc_pending _ = Some ?y |- _ =>
           is_var y; rewrite Hsvc in Hp; injection Hp as <-
       end.
  all: match goal with
       | Hsp : syscall_spec _ _ (Ok _ _ _) |- _ =>
           destruct (xc_spec_inv _ _ _ _ Hsp) as (? & _ & _ & -> & _)
       end.
  all: first
    [ exfalso; congruence
    | cbn [cfg_model];
      match goal with
      | Hm : materialize_model_accesses _ _ = Some _ |- _ =>
          rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hm;
          injection Hm as <-; exact Hnh
      end ].
Qed.

(** THE CASE: the one-step run with the zero image logs [xc_call]: the
    record carries the 24 bytes the call stored. *)
Example xc_capget_logged : forall segs,
  star_calls segs xc_cfg [] [xc_call] xc_after.
Proof.
  intros segs.
  replace [xc_call] with
    [mkSysCall (Z_to_bv 64 90) (syscall_args xc_ms) (eff_ret xc_eff)
       (eff_writes xc_eff) (eff_zeros xc_eff)] by check_eq.
  change (@nil event) with (@nil event ++ @nil event).
  apply (star_calls_ret segs xc_ms xb_model (Z_to_bv 64 90) xc_eff
           xb_model xb_model [] [] [] xc_after).
  - vm_compute. reflexivity.
  - reflexivity.
  - apply xc_spec_ok.
  - vm_compute. reflexivity.
  - apply materialize_model_accesses_no_lazy. vm_compute. reflexivity.
  - apply star_calls_refl.
Qed.

(** THE LOG HOLDS WHAT WAS STORED: every logged run from [xc_cfg] is the
    empty one, or its log starts with number 90, a0..a5, 0, one
    copy-out of 24 bytes at the destination whose effective and
    permitted words are 0, and no zero-filled range. *)
Example xc_capget_log_head : forall segs tr log c',
  star_calls segs xc_cfg tr log c' ->
  (tr = [] /\ log = [] /\ c' = xc_cfg) \/
  exists bs rest,
    log = mkSysCall (Z_to_bv 64 90) xc_args (Z_to_bv 64 0) [(xc_dst, bs)] [] :: rest
    /\ capget_data_ok bs = true.
Proof.
  intros segs tr log c' H.
  assert (Hsvc : ms_svc_pending xc_ms = Some (Z_to_bv 64 90)) by reflexivity.
  unfold xc_cfg in H. inversion H; subst.
  - left. repeat split.
  - right.
    match goal with
    | Hp : ms_svc_pending _ = Some ?y |- _ =>
        is_var y; rewrite Hsvc in Hp; injection Hp as <-
    end.
    match goal with
    | Hsp : syscall_spec _ _ (Ok _ _ _) |- _ =>
        destruct (xc_spec_inv _ _ _ _ Hsp) as (bs & -> & Hbs & _ & _)
    end.
    match goal with |- exists _ _, _ :: ?l = _ /\ _ => exists bs, l end.
    rewrite xc_args_at. split; [reflexivity | exact Hbs].
  - exfalso.
    match goal with
    | Hs : sstep _ _ _ (SNext _), Hor : _ \/ _ |- _ =>
        pose proof (xc_next_not_halted _ _ _ Hs) as Hc2;
        destruct Hor as [Hn | Hh];
        [ cbn [cfg_ms] in Hn; congruence | exact (Hh Hc2) ]
    end.
Qed.

(** A permitted capability in the image: uid 1000 holds none. *)
Definition xc_image_perm : list byte :=
  repeat (Z_to_bv 8 0) 4 ++ repeat (Z_to_bv 8 255) 4 ++ repeat (Z_to_bv 8 0) 16.

(** Two logs no run from [xc_cfg] has: the record without its store,
    and the record whose stored image claims a permitted capability. *)
Example xc_capget_other_logs_refused : forall segs tr rest c',
  ~ star_calls segs xc_cfg tr
      (mkSysCall (Z_to_bv 64 90) xc_args (Z_to_bv 64 0) [] [] :: rest) c' /\
  ~ star_calls segs xc_cfg tr
      (mkSysCall (Z_to_bv 64 90) xc_args (Z_to_bv 64 0) [(xc_dst, xc_image_perm)] []
       :: rest) c'.
Proof.
  intros segs tr rest c'. split; intros H;
    destruct (xc_capget_log_head _ _ _ _ H) as [(_ & Hl & _) | (bs & r & Hl & Hbs)];
    [ discriminate Hl
    | apply (f_equal (fun l => length (sc_writes (hd xc_call l)))) in Hl;
      vm_compute in Hl; discriminate Hl
    | discriminate Hl
    | apply (f_equal (fun l => match sc_writes (hd xc_call l) with
                               | (_, b) :: _ => b
                               | [] => []
                               end)) in Hl;
      vm_compute in Hl; subst bs; vm_compute in Hbs; discriminate Hbs ].
Qed.

(** THE CONTROL: the same run is a [star] run. *)
Example xc_capget_star : forall segs, star segs xc_cfg [] xc_after.
Proof. intros segs. exact (star_calls_star _ _ _ _ _ (xc_capget_logged segs)). Qed.

(* =========================================================================
   A call that ends the process is in the trace, not in the log
   ========================================================================= *)

(** exit_group(3) at the same registers: the model after it is halted
    with status 3. *)
Definition xb_exit_model : Model := with_halted (Z_to_bv 64 3) xb_model.

Definition xb_exit_ms : machine_state :=
  set_reg (xb_call_ms 94) (Z_to_bv 5 10) (Z_to_bv 64 3).

Definition xb_exit_cfg : config := mkCfg xb_exit_ms xb_model.

Lemma xb_exit_spec_det : forall segs eff m' evs,
  syscall_spec (sys_input segs xb_exit_ms (Z_to_bv 64 94)) xb_model
    (Ok eff m' evs) ->
  eff = mkEffect (Z_to_bv 64 0) [] [] /\ m' = xb_exit_model /\ evs = [].
Proof.
  intros segs eff m' evs H.
  apply check_syscall_complete_ok in H.
  rewrite check_syscall_exit_group in H by (vm_compute; reflexivity).
  unfold check_exit in H. apply check_ret_only_ok_iff in H.
  destruct H as (-> & -> & ->). split; [reflexivity|split; [|reflexivity]].
  unfold xb_exit_model. f_equal. check_eq.
Qed.

(** No step leaves a halted configuration, so its only logged run is
    the empty one. *)
Lemma xb_star_calls_halted : forall segs c tr log c',
  m_halted (cfg_model c) <> None ->
  star_calls segs c tr log c' -> log = [].
Proof.
  intros segs c tr log c' Hh H.
  inversion H; subst.
  - reflexivity.
  - exfalso. cbn [cfg_model] in Hh. contradiction.
  - exfalso.
    match goal with Hs : sstep _ _ _ _ |- _ => inversion Hs; subst end;
      cbn [cfg_model] in Hh; contradiction.
Qed.

(** THE CASE: the run through exit_group carries the exit in its trace
    and an empty log ... *)
Example xb_exit_logged : forall segs,
  star_calls segs xb_exit_cfg
    [ExitEv (Z_to_bv 64 3) (m_fs xb_exit_model)] [] (mkCfg xb_exit_ms xb_exit_model).
Proof.
  intros segs.
  change [ExitEv (Z_to_bv 64 3) (m_fs xb_exit_model)]
    with (([] ++ [ExitEv (Z_to_bv 64 3) (m_fs xb_exit_model)]) ++ []).
  eapply star_calls_other; [| |apply star_calls_refl].
  - unfold xb_exit_cfg.
    eapply (sstep_exit segs xb_exit_ms xb_model (Z_to_bv 64 94)
              (mkEffect (Z_to_bv 64 0) [] []) xb_exit_model [] (Z_to_bv 64 3)).
    + vm_compute. reflexivity.
    + reflexivity.
    + apply check_syscall_sound_ok.
      rewrite check_syscall_exit_group by (vm_compute; reflexivity).
      check_eq.
    + reflexivity.
    + vm_compute. reflexivity.
  - right. cbn [cfg_model]. intros Hc. vm_compute in Hc. discriminate Hc.
Qed.

(** ... and every logged run from [xb_exit_cfg] has an empty log: the
    call returns to nobody, so it is never recorded. *)
Example xb_exit_log_empty : forall segs tr log c',
  star_calls segs xb_exit_cfg tr log c' -> log = [].
Proof.
  intros segs tr log c' H.
  assert (Hsvc : ms_svc_pending xb_exit_ms = Some (Z_to_bv 64 94)) by reflexivity.
  unfold xb_exit_cfg in H. inversion H; subst.
  - reflexivity.
  - exfalso.
    match goal with
    | Hp : ms_svc_pending _ = Some ?y |- _ =>
        is_var y; rewrite Hsvc in Hp; injection Hp as <-
    end.
    match goal with
    | Hsp : syscall_spec _ _ (Ok _ _ _) |- _ =>
        destruct (xb_exit_spec_det _ _ _ _ Hsp) as (_ & -> & _)
    end.
    match goal with
    | Hz : m_halted xb_exit_model = None |- _ => vm_compute in Hz; discriminate Hz
    end.
  - match goal with
    | Hs : sstep _ _ _ (SNext ?c2), Hr : star_calls _ ?c2 _ _ _ |- _ =>
        eapply (xb_star_calls_halted segs c2 _ _ _); [|exact Hr];
        inversion Hs; subst; try congruence
    end.
    all: match goal with
         | Hp : ms_svc_pending _ = Some ?y |- _ =>
             is_var y; rewrite Hsvc in Hp; injection Hp as <-
         end.
    all: match goal with
         | Hsp : syscall_spec _ _ (Ok _ _ _) |- _ =>
             destruct (xb_exit_spec_det _ _ _ _ Hsp) as (_ & -> & _)
         end.
    all: first
      [ match goal with
        | Hz : m_halted xb_exit_model = None |- _ =>
            exfalso; vm_compute in Hz; discriminate Hz
        end
      | cbn [cfg_model]; intros Hc; vm_compute in Hc; discriminate Hc ].
Qed.
