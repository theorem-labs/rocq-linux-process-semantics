(** * LinuxProcessSem.Checks.Witness.Mm.Mprotect — the mprotect (226) witnesses, and their proofs

    Mirrors [Sys/Mm/Mprotect.v], which answers to Linux [mm/mprotect.c]:
    this file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude.

Definition mprotect_witness (addr len prot : word) (m : Model)
    : outcome SyscallEffect :=
  if mprotect_grows_conflict_b prot
  then ret_outcome (errno_ret EINVAL) m
  else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
  then ret_outcome (errno_ret EINVAL) m
  else if w_is0 len then ret_outcome (Z_to_bv 64 0) m
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z
  then ret_outcome (errno_ret ENOMEM) m
  else if mprotect_modeled_b prot then
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    if map_contains (vm_noaccess (m_vmmaps m)) addr n
       && map_contains (vm_maps (m_vmmaps m)) addr n
    then ret_outcome (errno_ret witness_errno) m
    else if map_contains (vm_maps (m_vmmaps m)) addr n
            && region_free (vm_noaccess (m_vmmaps m)) addr n
         then ret_outcome (Z_to_bv 64 0) m
         else if vdso_byte (m_vdso m) (bv_unsigned addr)
         then (if vdso_vvar_byte (m_vdso m) (bv_unsigned addr)
               then ret_outcome (errno_ret EACCES) m
               else if vdso_split (m_vdso m) (bv_unsigned addr)
                         (bv_unsigned addr + nZ)
               then ret_outcome (errno_ret EINVAL) m
               else Unmodeled)
         else Unmodeled
  else Unmodeled.

Lemma mprotect_witness_ok : forall addr len prot i m,
  mprotect_spec addr len prot i m (mprotect_witness addr len prot m).
Proof.
  intros. unfold mprotect_spec, mprotect_witness.
  destruct (mprotect_grows_conflict_b prot) eqn:Hgrows; [apply pure_ok|].
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign;
    [apply pure_ok|].
  destruct (w_is0 len) eqn:Hlen; [apply pure_ok|].
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig; [apply pure_ok|].
  destruct (mprotect_modeled_b prot) eqn:Hprot; [|apply unmodeled_intro].
  eapply bind_step; [apply get_model_ok|]. cbv beta zeta.
  destruct (map_contains (vm_noaccess (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hcover.
  { apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok. }
  destruct (map_contains (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && region_free (vm_noaccess (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hfree.
  { apply pure_ok. }
  destruct (vdso_byte (m_vdso m) (bv_unsigned addr)) eqn:Hvb;
    [|apply unmodeled_intro].
  cbv beta iota. unfold mprotect_vdso.
  destruct (vdso_vvar_byte (m_vdso m) (bv_unsigned addr)); [apply pure_ok|].
  destruct (vdso_split (m_vdso m) (bv_unsigned addr)
              (bv_unsigned addr + page_round_up_Z (bv_unsigned len)));
    [apply alt_r; apply pure_ok | apply unmodeled_intro].
Qed.
