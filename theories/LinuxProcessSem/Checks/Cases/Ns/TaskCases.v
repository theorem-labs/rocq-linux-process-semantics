(** * LinuxProcessSem.Checks.Cases.Ns.TaskCases — capabilities and prctl on a task's own state

    Each example runs one arm of [Ns.Task] on a task whose capability sets,
    parent-death signal, no_new_privs bit and dumpable mode the namespace
    model holds, and states its exact answer. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Userns Task.
Import ListNotations.
Open Scope Z_scope.

(** Bytes [bs] at address [base], nothing else mapped. *)
Definition at_ (base : Z) (bs : list Z) : word -> option byte :=
  fun a => let k := bv_unsigned a - base in
           if (0 <=? k) && (k <? Z.of_nat (length bs)) then Some (Z_to_bv 8 (nth (Z.to_nat k) bs 0))
           else None.

Definition le32 (v : Z) : list Z := map (fun b => Z.land (Z.shiftr v (8 * b)) 255) [0; 1; 2; 3].

Definition HDR : Z := 8192.
Definition DATA : Z := 12288.

(** A header (version, pid) at [HDR], 24 data bytes at [DATA]; the data is
    writable, the header is. *)
Definition mem (version pid : Z) (data : list Z) : word -> option byte :=
  fun a => match at_ HDR (le32 version ++ le32 pid) a with
           | Some b => Some b
           | None => at_ DATA data a
           end.

Definition call (n : Z) (args : list Z) (mm : word -> option byte) : SyscallInput :=
  mkInput (Z_to_bv 64 n) (map (Z_to_bv 64) args) mm mm.

(** A task with pid 2 in namespace 1 and the given sets, signal, bit and
    mode. *)
Definition task (c : CapSets) (sig : Z) (nnp : bool) (dump : Z) : NsCtx :=
  mkNsCtx 1 1 1 1 [(1%positive, 2)] (1%positive, 1%positive) (1%positive, 1%positive) 18 c 0 []
          nnp sig dump.

Definition U : NsState :=
  with_userns empty_nsstate [mkUserNs 1 None 0 0 None None true true INT_MAX true].

Definition sys_admin : Z := 2 ^ 21.
Definition setpcap : Z := 2 ^ 8.
Definition full : Z := 2 ^ 41 - 1.

Definition caps0 : CapSets := mkCaps (Z.lor sys_admin setpcap) (Z.lor sys_admin setpcap) 0 full 0.

Definition ret_of (o : ext_outcome) : option Z :=
  match o with EOk eff _ _ _ _ => Some (bv_signed (eff_ret eff)) | EUnmodeled => None end.
Definition writes_of (o : ext_outcome) : option (list (Z * list Z)) :=
  match o with
  | EOk eff _ _ _ _ => Some (map (fun p => (bv_unsigned (fst p), map bv_unsigned (snd p))) (eff_writes eff))
  | EUnmodeled => None
  end.
Definition caps_of (o : ext_outcome) : option CapSets :=
  match o with EOk _ _ ctx _ _ => Some (cx_caps ctx) | EUnmodeled => None end.
Definition ctx_of (o : ext_outcome) : option NsCtx :=
  match o with EOk _ _ ctx _ _ => Some ctx | EUnmodeled => None end.

Definition V3 : Z := LINUX_CAPABILITY_VERSION_3.

(** [capget] of the caller: the three sets, low halves then high halves. *)
Example capget_own_sets : forall m,
  writes_of (capget_fn (call 90 [HDR; DATA] (mem V3 0 (repeat 0 24))) m (task caps0 0 false 1) U)
  = Some [(DATA, le32 (Z.lor sys_admin setpcap) ++ le32 (Z.lor sys_admin setpcap) ++ le32 0
                 ++ le32 0 ++ le32 0 ++ le32 0)].
Proof. intros m. vm_compute. reflexivity. Qed.

(** A version the kernel does not know: version 3 written back, EINVAL;
    with a NULL data pointer, 0. *)
Example capget_bad_version : forall m,
  ret_of (capget_fn (call 90 [HDR; DATA] (mem 1 0 (repeat 0 24))) m (task caps0 0 false 1) U)
  = Some (-22).
Proof. intros m. vm_compute. reflexivity. Qed.
Example capget_bad_version_null : forall m,
  writes_of (capget_fn (call 90 [HDR; 0] (mem 1 0 [])) m (task caps0 0 false 1) U)
  = Some [(HDR, le32 V3)].
Proof. intros m. vm_compute. reflexivity. Qed.

(** A negative pid is EINVAL; the caller's own pid is the caller. *)
Example capget_negative_pid : forall m,
  ret_of (capget_fn (call 90 [HDR; DATA] (mem V3 4294967295 (repeat 0 24))) m (task caps0 0 false 1) U)
  = Some (-22).
Proof. intros m. vm_compute. reflexivity. Qed.
Example capget_own_pid : forall m,
  ret_of (capget_fn (call 90 [HDR; DATA] (mem V3 2 (repeat 0 24))) m (task caps0 0 false 1) U)
  = Some 0.
Proof. intros m. vm_compute. reflexivity. Qed.

(** [capset] to empty sets: every set but the bounding set empties. *)
Example capset_drop_all : forall m,
  caps_of (capset_fn (call 91 [HDR; DATA] (mem V3 0 (repeat 0 24))) m (task caps0 0 false 1) U)
  = Some (mkCaps 0 0 0 full 0).
Proof. intros m. vm_compute. reflexivity. Qed.

(** Raising a permitted bit the task does not hold is EPERM. *)
Example capset_raise_refused : forall m,
  ret_of (capset_fn (call 91 [HDR; DATA] (mem V3 0 (le32 0 ++ le32 1 ++ le32 0 ++ repeat 0 12)))
                    m (task caps0 0 false 1) U)
  = Some (-1).
Proof. intros m. vm_compute. reflexivity. Qed.

(** Another task's pid is EPERM. *)
Example capset_other_pid : forall m,
  ret_of (capset_fn (call 91 [HDR; DATA] (mem V3 3 (repeat 0 24))) m (task caps0 0 false 1) U)
  = Some (-1).
Proof. intros m. vm_compute. reflexivity. Qed.

(** PR_CAPBSET_DROP needs CAP_SETPCAP, then a valid number. *)
Example bset_drop : forall m,
  option_map cap_bounding (caps_of (prctl_fn (call 167 [24; 21; 0; 0; 0] (fun _ => None)) m
                                              (task caps0 0 false 1) U))
  = Some (full - sys_admin).
Proof. intros m. vm_compute. reflexivity. Qed.
Example bset_drop_needs_setpcap : forall m,
  ret_of (prctl_fn (call 167 [24; 21; 0; 0; 0] (fun _ => None)) m
                   (task (mkCaps 0 0 0 full 0) 0 false 1) U) = Some (-1).
Proof. intros m. vm_compute. reflexivity. Qed.
Example bset_drop_invalid : forall m,
  ret_of (prctl_fn (call 167 [24; 41; 0; 0; 0] (fun _ => None)) m (task caps0 0 false 1) U)
  = Some (-22).
Proof. intros m. vm_compute. reflexivity. Qed.

Example bset_read : forall m,
  ret_of (prctl_fn (call 167 [23; 21; 0; 0; 0] (fun _ => None)) m
                   (task (mkCaps 0 0 0 (full - sys_admin) 0) 0 false 1) U) = Some 0.
Proof. intros m. vm_compute. reflexivity. Qed.

(** The parent-death signal: set, then read into user memory. *)
Example pdeathsig_set : forall m,
  option_map cx_pdeathsig (ctx_of (prctl_fn (call 167 [1; 9; 0; 0; 0] (fun _ => None)) m
                                            (task caps0 0 false 1) U)) = Some 9.
Proof. intros m. vm_compute. reflexivity. Qed.
Example pdeathsig_invalid : forall m,
  ret_of (prctl_fn (call 167 [1; 65; 0; 0; 0] (fun _ => None)) m (task caps0 0 false 1) U)
  = Some (-22).
Proof. intros m. vm_compute. reflexivity. Qed.
Example pdeathsig_get : forall m,
  writes_of (prctl_fn (call 167 [2; DATA; 0; 0; 0] (at_ DATA (repeat 0 4))) m (task caps0 9 false 1) U)
  = Some [(DATA, le32 9)].
Proof. intros m. vm_compute. reflexivity. Qed.

(** no_new_privs: set with exactly (1, 0, 0, 0), read with all zero. *)
Example nnp_set : forall m,
  option_map cx_no_new_privs (ctx_of (prctl_fn (call 167 [38; 1; 0; 0; 0] (fun _ => None)) m
                                               (task caps0 0 false 1) U)) = Some true.
Proof. intros m. vm_compute. reflexivity. Qed.
Example nnp_set_bad_args : forall m,
  ret_of (prctl_fn (call 167 [38; 1; 1; 0; 0] (fun _ => None)) m (task caps0 0 false 1) U)
  = Some (-22).
Proof. intros m. vm_compute. reflexivity. Qed.
Example nnp_get : forall m,
  ret_of (prctl_fn (call 167 [39; 0; 0; 0; 0] (fun _ => None)) m (task caps0 0 true 1) U) = Some 1.
Proof. intros m. vm_compute. reflexivity. Qed.

(** The dumpable mode: 0 or 1 only. *)
Example dumpable_set : forall m,
  option_map cx_dumpable (ctx_of (prctl_fn (call 167 [4; 0; 0; 0; 0] (fun _ => None)) m
                                           (task caps0 0 false 1) U)) = Some 0.
Proof. intros m. vm_compute. reflexivity. Qed.
Example dumpable_invalid : forall m,
  ret_of (prctl_fn (call 167 [4; 2; 0; 0; 0] (fun _ => None)) m (task caps0 0 false 1) U)
  = Some (-22).
Proof. intros m. vm_compute. reflexivity. Qed.

(** Any other option declines. *)
Example prctl_other_declines : forall m,
  prctl_fn (call 167 [15; 0; 0; 0; 0] (fun _ => None)) m (task caps0 0 false 1) U = EUnmodeled.
Proof. intros m. vm_compute. reflexivity. Qed.
