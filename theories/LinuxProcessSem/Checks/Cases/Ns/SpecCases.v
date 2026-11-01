(** * LinuxProcessSem.Checks.Cases.Ns.SpecCases — which calls the namespace model answers

    [Ns.Spec.ns_ext] claims every call but [clone] (220) and [wait4]
    (260), which the core answers, and the extension that claims nothing
    claims nothing.  In the released world a claimed call has exactly the
    released answers ([ns_spec_flat]). *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Spec.
Import ListNotations.
Open Scope bv_scope.

Definition call (n : word) : SyscallInput := mkInput n [] (fun _ => None) (fun _ => None).

Example ns_leaves_clone : ext_claims ns_ext (call 220) = false := eq_refl.
Example ns_leaves_wait4 : ext_claims ns_ext (call 260) = false := eq_refl.
Example ns_claims_openat : ext_claims ns_ext (call 56) = true := eq_refl.
Example ns_claims_mount : ext_claims ns_ext (call 40) = true := eq_refl.
Example ns_claims_exit_group : ext_claims ns_ext (call 94) = true := eq_refl.

Example no_ext_leaves_openat : ext_claims no_ext (call 56) = false := eq_refl.

(** The released world is the one a core builds from [empty_nsstate]. *)
Example empty_is_flat : flat_view empty_nsstate = true := eq_refl.

(** A world with a mount tree is not the released world, and there a
    number with no arm fails closed. *)
Definition one_mount : NsState :=
  with_mounts empty_nsstate
    [mkMount 1 1 None 1 1 1 (mkMountFlags false false false false)
             (mkMountFlags false false false false) false false None None].

Example mounted_not_flat : flat_view one_mount = false := eq_refl.

Example unlisted_fails_closed : forall m ctx o,
  ns_spec (call 9999) m ctx one_mount o <-> o = EUnmodeled.
Proof. intros m ctx o. vm_compute. tauto. Qed.

(** A task with pid 2 in its pid namespace 1 and umask 022. *)
Definition task (pid : Z) (umask : Z) : NsCtx :=
  mkNsCtx 1 1 1 1 [(1%positive, pid)] (1%positive, 1%positive) (1%positive, 1%positive) umask
          (mkCaps 0 0 0 0 0) 0 [] false 0 1.

Example getpid_own_pid : forall m,
  ns_spec (call 172) m (task 2 18) one_mount (ns_ret (Z_to_bv 64 2) m (task 2 18) one_mount).
Proof. intros m. vm_compute. reflexivity. Qed.

Example gettid_own_pid : forall m,
  ns_spec (call 178) m (task 2 18) one_mount (ns_ret (Z_to_bv 64 2) m (task 2 18) one_mount).
Proof. intros m. vm_compute. reflexivity. Qed.

(** [umask (0777 | 01000)]: the old mask back, the permission bits kept. *)
Definition call1 (n a : word) : SyscallInput := mkInput n [a] (fun _ => None) (fun _ => None).

Example umask_swaps : forall m,
  ns_spec (call1 166 1023) m (task 2 18) one_mount (ns_ret (Z_to_bv 64 18) m (task 2 511) one_mount).
Proof. intros m. vm_compute. reflexivity. Qed.

(** In the released world the same calls are the released model's. *)
Example getpid_flat_is_released : forall m ctx o,
  ns_spec (call 172) m ctx empty_nsstate o <-> released (call 172) m ctx empty_nsstate o.
Proof. intros m ctx o. apply ns_spec_flat. reflexivity. Qed.
