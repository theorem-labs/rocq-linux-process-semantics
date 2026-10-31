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
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples.
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

(** "/tmp", the second word of every grade argv's [--tmpfs /tmp]. *)
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
