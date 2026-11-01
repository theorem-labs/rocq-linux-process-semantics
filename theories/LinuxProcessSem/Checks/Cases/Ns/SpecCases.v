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
Proof. intros m ctx o. unfold ns_spec. cbn. reflexivity. Qed.
