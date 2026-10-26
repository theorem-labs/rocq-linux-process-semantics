(** * LinuxProcessSem.Checks.BudgetPremiseInv — the move's budget gate on invariant states

    Not part of the trusted specification.  [BudgetPremise]'s
    [mremap_move_budget_admits_fresh_lazyfree] takes two ledger
    hypotheses, [State.noaccess_pages_owned] and the fit of the live
    mappings.  Both follow from [NoaccessOwned.sys_inv], which
    [execve] establishes and every modeled syscall preserves
    ([NoaccessOwned.init_model_sys_inv],
    [NoaccessOwned.syscall_spec_preserves_sys_inv]); this file states
    the gate fact with that one hypothesis in their place. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs BudgetPremise MapsFit NoaccessOwned.
Import ListNotations.
Open Scope bv_scope.

Corollary mremap_move_budget_admits_fresh_sys_inv :
  forall m old old_n dst new_n,
  sys_inv (m_vmmaps m) ->
  m_vm_lazy m = [] ->
  m_vm_materialized m = [] ->
  (bv_unsigned dst mod page_size = 0)%Z ->
  (bv_unsigned new_n mod page_size = 0)%Z ->
  (0 < bv_unsigned new_n)%Z ->
  (bv_unsigned dst + bv_unsigned new_n <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) dst new_n
  = true ->
  mremap_move_budget_b m old old_n new_n = true ->
  mremap_final_budget_b m old old_n dst new_n = true.
Proof.
  intros m old old_n dst new_n Hinv Hlz Hmat Hdalign Hnmod Hpos Hdtop Hdfree Hmv.
  destruct Hinv as (Hwf & Hfit & Hna).
  exact (mremap_move_budget_admits_fresh_lazyfree m old old_n dst new_n
           Hlz Hmat Hdalign Hnmod Hpos Hdtop Hdfree
           (sys_inv_noaccess_pages_owned _ (conj Hwf (conj Hfit Hna)))
           (vm_fit_map_remove _ old Hfit) Hmv).
Qed.
