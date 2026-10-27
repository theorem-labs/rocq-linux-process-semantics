(** * LinuxProcessSem.Checks.BudgetPremise — the budget mark, on cases chosen by hand

    Not part of the trusted specification: QA on [Run.budget_refused_at],
    [Run.alloc_budget_refused_b], the per-arm marks beside the allocation
    specs, and the budget-parameterised statements of
    [Equivalence.SpecBudgets], written to be READ, in the manner of
    [Checks.Examples] and under the four admission reasons its header
    lists.  Every case here is one a single real run cannot show:
    the mark is a statement about what the BUDGET leaves the kernel
    (reason 3, a model constant and model-internal state), and the
    run-level cases quantify over every execution (reason 1).

    ** What is pinned

    - PART 1, the grant clause, arm by arm.  Each mark fires on the
      arm's own beyond-budget fixture and does not fire within budget,
      on a request an argument gate answers, on a request that consumes
      no backing, or on a query — so a budget refusal is distinguishable
      from every other refusal the arm admits.  Beside the fixtures, the
      SOUNDNESS lemmas at abstract arguments: where the mark fires,
      every outcome the arm admits is a refusal ([Run.refusal_b]) — for
      [brk], [mmap] and [mprotect] over the whole arm; for [mremap] the
      in-place resolution on every state, and the moved one at every
      destination that carries no backing metadata (the mark's header
      in [Sys/Mm/Mremap.v] gives the rule).  Beside it, the
      COMPLETENESS lemma: in-place growth not admitted and the move's
      gate refusing at a fresh destination fires the mark; and the
      lemma that the mark is weaker than the earlier two-gate mark.
    - PART 2, the two first-touch clauses.  A store into a lazy page
      with the budget spent IS budget-refused and is an [SError]
      transition; the same store with a page of budget left is not; and
      a fault the interpreter raises for its own reasons — the [ebreak]
      of [Checks.Omni] — is not, although it takes the same transition.
      A syscall whose copy-in touches a lazy page with the budget spent
      is budget-refused through the effect clause.
    - PART 3, the dispatcher: every [FamAlloc] arm and nothing else
      ([Run.alloc_family_dispatched] makes the enumeration a theorem).
    - PART 4, run level.  The exit-0 image never reaches the mark at ANY
      budget, entry or input, through the same reflective evaluator that
      discharges [MustExit] ([Checks.Examples.exits_c]); a six-instruction
      image that asks for two pages at a one-page budget DOES reach it —
      the premise bites, so the budget family is not the constant-pinned
      family under another name; and the exit-0 pair seals
      [Equivalence.SPEC_ERROR_FREE_BUDGETS] and its abort twin under the
      shipped budgets — the ascription a Checker generated for a flavour
      pair will make.  [tools/gen_checker.py] does not emit it yet, so
      the surface is unconsumed until the generator is taught it.

    A forged budget refusal is not a thing a trace can carry: the mark
    reads the request and the state and never an answer, so "budget
    refused where none occurred" is the within-budget fixture, on which
    the mark is [false] although the -ENOMEM the arm keeps under [alt]
    is admissible.  The forged GRANT beyond budget is the checker's
    [CheckReject], already pinned by
    [Checks.Cases.Mm.Mmap.mmap_beyond_budget_rejected] and
    [Checks.Cases.Mm.Mmap.brk_grow_beyond_budget_rejects_moving], and not
    repeated here.

    ** Computing on a machine state without reading it back

    As in [Checks.Omni]: every [vm_compute] below closes a SCALAR — a
    boolean, an access list, a checker verdict — and the run-level image
    is stepped with its memory abstracted ([Checks.Omni.with_mem]). *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs Examples SpuriousCfg Omni AbortWitness.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit Classifier OmniEquivalence.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* =========================================================================
   PART 1 — the grant clause, arm by arm
   ========================================================================= *)

(** ** brk

    [Checks.Cases.Mm.Mmap.m_tight_brk]: a fresh process with a one-page
    budget and its break at 65536.  A two-page grow is refused for
    budget; a one-page grow fits; the query is not a request. *)

Example brk_two_pages_is_budget_refused :
  brk_budget_refused_b m_tight_brk 73728 = true.
Proof. vm_compute. reflexivity. Qed.

Example brk_one_page_is_not_budget_refused :
  brk_budget_refused_b m_tight_brk 69632 = false.
Proof. vm_compute. reflexivity. Qed.

Example brk_query_is_not_budget_refused :
  brk_budget_refused_b m_tight_brk 0 = false.
Proof. vm_compute. reflexivity. Qed.

(** After the one-page grow the budget is spent: a single further byte
    is refused, and a shrink back is not a budget refusal (it releases). *)
Definition m_tight_brk_grown : Model :=
  with_vmmaps (mkVmMaps brk_reserved [(65536, 4096)] 65536 69632 4096) m_tight_brk.

Example brk_one_byte_on_spent_budget_is_budget_refused :
  brk_budget_refused_b m_tight_brk_grown 69633 = true.
Proof. vm_compute. reflexivity. Qed.

Example brk_shrink_is_not_budget_refused :
  brk_budget_refused_b m_tight_brk_grown 65536 = false.
Proof. vm_compute. reflexivity. Qed.

(** SOUNDNESS, abstract: where the mark fires, [Mmap.brk_r_ok] admits
    only the unmoved break. *)
Lemma brk_budget_refused_forces : forall m req r,
  brk_budget_refused_b m req = true ->
  brk_r_ok m req r = true ->
  r = vm_brk (m_vmmaps m).
Proof.
  intros m req r Hmark Hok.
  unfold brk_budget_refused_b in Hmark. unfold brk_r_ok in Hok. cbv zeta in *.
  destruct (w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps m))))
    eqn:E1; [discriminate Hmark |].
  cbn [negb andb] in Hmark.
  destruct (Z.ltb 0 (bv_unsigned (vm_brk (m_vmmaps m)))) eqn:E2; [| discriminate Hmark].
  destruct (Z.ltb (bv_unsigned (vm_brk (m_vmmaps m))) (bv_unsigned req)) eqn:E3;
    [| discriminate Hmark].
  cbn [andb] in Hmark.
  assert (E4 : Z.ltb (bv_unsigned req) (bv_unsigned (vm_brk (m_vmmaps m))) = false)
    by (apply Z.ltb_ge; apply Z.ltb_lt in E3; lia).
  rewrite E4 in Hok.
  apply andb_true_iff in Hok as [Hr Hgrow].
  apply orb_true_iff in Hr as [Hr | Hr]; [| apply bv_eqb_eq in Hr; exact Hr].
  apply bv_eqb_eq in Hr. subst r. exfalso.
  unfold brk_grow_ok in Hgrow. cbv zeta in Hgrow. rewrite E2, E3 in Hgrow.
  cbn [andb] in Hgrow.
  apply andb_true_iff in Hgrow as [_ Hbud]. rewrite Hbud in Hmark. discriminate Hmark.
Qed.

Lemma brk_dispatch : forall i m o,
  bv_unsigned (in_sysno i) = 214%Z ->
  syscall_spec i m o <-> brk_spec (in_arg i 0) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

(** ... hence, through the dispatcher, every admitted outcome is one of
    [Run.refusal_b]'s refusals. *)
Lemma brk_budget_refused_is_refusal : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 214%Z ->
  alloc_budget_refused_b i m = true ->
  syscall_spec i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m eff m' evs E Hmark Hspec.
  unfold alloc_budget_refused_b in Hmark. rewrite E, Z.eqb_refl in Hmark.
  apply (proj1 (brk_dispatch i m _ E)) in Hspec.
  unfold brk_spec, bind, get_model, choose, modify, pure in Hspec.
  cbv beta zeta in Hspec. sys_destruct.
  match goal with
  | [ Hok : brk_r_ok m (in_arg i 0) ?r = true |- _ ] =>
      pose proof (brk_budget_refused_forces _ _ _ Hmark Hok) as Hr; subst r
  end.
  cbn [eff_ret]. unfold refusal_b. rewrite E, Z.eqb_refl.
  unfold brk_refusal_b. unfold brk_budget_refused_b in Hmark. cbv zeta in *.
  apply andb_true_iff in Hmark as [Hmark _].
  apply andb_true_iff in Hmark as [Hmark H3].
  apply andb_true_iff in Hmark as [H1 H2].
  apply negb_true_iff in H1. apply orb_false_iff in H1 as [H1a H1b].
  rewrite H1a, H1b. cbn [negb andb].
  rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
  destruct (bv_eqb (in_arg i 0) (vm_brk (m_vmmaps m))) eqn:Eq; [| reflexivity].
  apply bv_eqb_eq in Eq. rewrite Eq, Z.ltb_irrefl in H3. discriminate H3.
Qed.

(** ** mmap

    [Checks.Cases.Prelude.tight_model]: budget 8192, one live page —
    one page of budget left.  [Checks.Cases.Mm.Mmap.mmap_in] is the
    hint-placed rw anonymous request. *)

Example mmap_two_pages_is_budget_refused :
  alloc_budget_refused_b (mmap_in 8192) tight_model = true.
Proof. vm_compute. reflexivity. Qed.

(** Within budget the mark is [false] — although the -ENOMEM is still
    admissible there ([Checks.SpuriousCfg.mmap_enomem_spurious_within_budget]):
    that is the "forged budget refusal", and the mark does not carry it. *)
Example mmap_one_page_is_not_budget_refused :
  alloc_budget_refused_b (mmap_in 4096) tight_model = false.
Proof. vm_compute. reflexivity. Qed.

(** A MAP_NORESERVE request beyond the budget is free at grant time
    and so not a budget refusal; its pages are charged on first touch
    (PART 2). *)
Definition mmap_noreserve_in (len : word) : SyscallInput :=
  mkInput 222 [0; len; 3; 16418; mmap_fd_none; 0] (fun _ => None) (fun _ => None).

Example mmap_noreserve_is_not_budget_refused :
  alloc_budget_refused_b (mmap_noreserve_in 8192) tight_model = false.
Proof. vm_compute. reflexivity. Qed.

(** A PROT_NONE reservation consumes no backing. *)
Definition mmap_noaccess_in (len : word) : SyscallInput :=
  mkInput 222 [0; len; 0; 34; mmap_fd_none; 0] (fun _ => None) (fun _ => None).

Example mmap_prot_none_is_not_budget_refused :
  alloc_budget_refused_b (mmap_noaccess_in 8192) tight_model = false.
Proof. vm_compute. reflexivity. Qed.

(** The -ENOMEM an ARGUMENT GATE determines — the overflowing MAP_FIXED
    length of [Checks.SpuriousCfg.mmap_overflow_i] — is not a budget
    refusal either, although it is in [Mmap.mmap_errnos]. *)
Example mmap_overflowing_len_is_not_budget_refused :
  alloc_budget_refused_b mmap_overflow_i noaccess_base = false.
Proof. vm_compute. reflexivity. Qed.

(** The contained MAP_FIXED rw commit, exposing a PROT_NONE page: on a
    spent budget it is refused; with a page left it is not. *)
Definition fixed_rw_model (lim : Z) : Model :=
  with_vmmaps
    (mkVmMapsFull [] [(65536, 4096)] [(65536, 4096)] 0 0 lim (Z_to_bv 64 0)
       (Z_to_bv 64 sp_window_lo))
    (init_model [] 0 0 demo_sp lim (demo_input [] IEof)).

Definition mmap_fixed_rw_in : SyscallInput :=
  mkInput 222 [65536; 4096; 3; 50; mmap_fd_none; 0] (fun _ => None) (fun _ => None).

Example mmap_fixed_commit_on_spent_budget_is_budget_refused :
  alloc_budget_refused_b mmap_fixed_rw_in (fixed_rw_model 0) = true.
Proof. vm_compute. reflexivity. Qed.

Example mmap_fixed_commit_within_budget_is_not_budget_refused :
  alloc_budget_refused_b mmap_fixed_rw_in (fixed_rw_model 4096) = false.
Proof. vm_compute. reflexivity. Qed.

(** The MAP_FIXED_NOREPLACE rw grant over a free range charges like any
    grant: beyond the remaining budget it is refused, within it not;
    the PROT_NONE spelling consumes nothing. *)
Definition mmap_noreplace_in (prot len : word) : SyscallInput :=
  mkInput 222 [131072; len; prot; 1048610; mmap_fd_none; 0] (fun _ => None) (fun _ => None).

Example mmap_noreplace_two_pages_is_budget_refused :
  alloc_budget_refused_b (mmap_noreplace_in 3 8192) tight_model = true.
Proof. vm_compute. reflexivity. Qed.

Example mmap_noreplace_one_page_is_not_budget_refused :
  alloc_budget_refused_b (mmap_noreplace_in 3 4096) tight_model = false.
Proof. vm_compute. reflexivity. Qed.

Example mmap_noreplace_prot_none_is_not_budget_refused :
  alloc_budget_refused_b (mmap_noreplace_in 0 8192) tight_model = false.
Proof. vm_compute. reflexivity. Qed.

(** The premise bites at 2 GiB too, not only at the shipped tight
    fixtures above: a FRESH model (no live grant) under the
    [Equivalence.sanitizer_source_limit] budget refuses an
    anonymous private request one page over that budget, and grants
    one of exactly that budget.  The ledger's arithmetic
    ([page_round_up_Z] against a plain [Z] comparison) is on
    page-rounded BYTE sizes, not a page count, but [Z] is binary, so
    [vm_compute] closes at this ~2 GiB magnitude in about the same
    time as the tight fixtures above; if that stops being true at a
    larger sealed budget, the check to change is this one, not the
    ledger. *)
Definition sanitizer_budget_model (lim : Z) : Model :=
  with_vmmaps (mkVmMaps [] [] 0 0 lim)
    (init_model [] 0 0 demo_sp lim (demo_input [] IEof)).

Example mmap_sanitizer_budget_plus_page_is_budget_refused :
  alloc_budget_refused_b
    (mmap_in (Z_to_bv 64 (sanitizer_source_limit + page_size)))
    (sanitizer_budget_model sanitizer_source_limit) = true.
Proof. vm_compute. reflexivity. Qed.

Example mmap_sanitizer_budget_exact_is_not_budget_refused :
  alloc_budget_refused_b
    (mmap_in (Z_to_bv 64 sanitizer_source_limit))
    (sanitizer_budget_model sanitizer_source_limit) = false.
Proof. vm_compute. reflexivity. Qed.

(** SOUNDNESS over the whole arm, abstract: where the mark fires, every
    admitted outcome is a refusal.  The proof walks [Mmap.mmap_spec]'s
    branches in the mark's order — the two are the same [if] chain —
    and in each charging branch the success resolution's budget
    conjunct contradicts the mark while the errno resolutions answer
    [Mmap.mmap_errnos]. *)
Ltac errno_is_refusal :=
  match goal with
  | [ Hin : In ?e mmap_errnos |- _ ] =>
      destruct Hin as [<- | []]; vm_compute; reflexivity
  end.

Lemma mmap_budget_refused_is_refusal : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 222%Z ->
  alloc_budget_refused_b i m = true ->
  syscall_spec i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m eff m' evs E Hmark Hspec.
  unfold alloc_budget_refused_b in Hmark. rewrite E in Hmark.
  cbn [Z.eqb Pos.eqb] in Hmark.
  apply (proj1 (mmap_dispatch i m _ E)) in Hspec.
  unfold refusal_b. rewrite E. cbv zeta.
  assert (Hne : (222 =? 214)%Z = false) by reflexivity. rewrite Hne.
  assert (Harm : injected_arm 222 = Some (mkInjectedArm 222 FamAlloc mmap_errnos))
    by reflexivity.
  rewrite Harm. cbn [ia_errnos].
  unfold mmap_budget_refused_b in Hmark. unfold mmap_spec in Hspec.
  revert Hmark Hspec.
  destruct (negb (mmap_off_aligned_b (in_arg i 5))); [intros Hmark; discriminate Hmark |].
  destruct (negb (mmap_anon_b (in_arg i 3))); [intros Hmark; discriminate Hmark |].
  destruct (w_is0 (in_arg i 1)); [intros Hmark; discriminate Hmark |].
  cbv zeta.
  destruct (mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5)).
  { intros Hmark Hspec.
    unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, get_model, modify
      in Hspec.
    cbv beta zeta in Hspec. sys_destruct.
    - errno_is_refusal.
    - match goal with
      | [ Hb : mmap_noreserve_backed_ok _ _ _ = true |- _ ] =>
          rewrite Hb in Hmark; discriminate Hmark
      end. }
  destruct (mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5));
    [intros Hmark; discriminate Hmark |].
  destruct (mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5));
    [intros Hmark; discriminate Hmark |].
  destruct (mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5)).
  {
  destruct (two_pow_64 <=? bv_unsigned (in_arg i 0)
                         + page_round_up_Z (bv_unsigned (in_arg i 1)))%Z;
    [intros Hmark; discriminate Hmark |].
  intros Hmark Hspec.
  unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, get_model, modify
    in Hspec.
  cbv beta zeta in Hspec. sys_destruct.
  match goal with
  | [ H : ?f i m (Ok eff m' ?e) |- _ ] => revert H
  end.
  revert Hmark.
  destruct (negb (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1))
                  <=? alloc_top (m_vmmaps m))%Z);
    [intros Hmark _; discriminate Hmark |].
  destruct (negb (Z.eqb (bv_unsigned (in_arg i 0) mod page_size) 0));
    [intros Hmark _; discriminate Hmark |].
  destruct (negb (0 <? bv_unsigned (in_arg i 0))%Z);
    [intros Hmark _; discriminate Hmark |].
  destruct (region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))
            && map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))).
  { intros Hmark Hspec. cbv beta iota zeta in Hspec. sys_destruct.
    - errno_is_refusal.
    - match goal with
      | [ Hb : mmap_fixed_rw_budget_ok _ _ _ _ = true |- _ ] =>
          rewrite Hb in Hmark; discriminate Hmark
      end.
    - errno_is_refusal. }
  destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))).
  { intros Hmark Hspec. cbv beta iota zeta in Hspec. sys_destruct.
    - errno_is_refusal.
    - match goal with
      | [ Hb : mmap_noreserve_backed_ok _ _ _ = true |- _ ] =>
          rewrite Hb in Hmark; discriminate Hmark
      end. }
  destruct (region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))));
    [| intros Hmark _; discriminate Hmark].
  intros Hmark Hspec. cbv beta iota zeta in Hspec. sys_destruct.
  - errno_is_refusal.
  - match goal with
    | [ Hb : mmap_fixed_rw_span_budget_ok _ _ _ _ = true |- _ ] =>
        rewrite Hb in Hmark; discriminate Hmark
    end.
  - errno_is_refusal.
  }
  (* the MAP_FIXED_NOREPLACE shapes: PROT_NONE consumes nothing; the rw
     one is the free-range MAP_FIXED grant with -EEXIST beside it *)
  destruct (mmap_noreplace_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5));
    [intros Hmark; discriminate Hmark |].
  destruct (mmap_noreplace_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5));
    [| intros Hmark; discriminate Hmark].
  destruct (two_pow_64 <=? bv_unsigned (in_arg i 0)
                         + page_round_up_Z (bv_unsigned (in_arg i 1)))%Z;
    [intros Hmark; discriminate Hmark |].
  intros Hmark Hspec.
  unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, get_model, modify
    in Hspec.
  cbv beta zeta in Hspec. sys_destruct.
  match goal with
  | [ H : ?f i m (Ok eff m' ?e) |- _ ] => revert H
  end.
  revert Hmark.
  destruct (negb (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1))
                  <=? alloc_top (m_vmmaps m))%Z);
    [intros Hmark _; discriminate Hmark |].
  destruct (negb (Z.eqb (bv_unsigned (in_arg i 0) mod page_size) 0));
    [intros Hmark _; discriminate Hmark |].
  destruct (negb (0 <? bv_unsigned (in_arg i 0))%Z);
    [intros Hmark _; discriminate Hmark |].
  destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))));
    [| intros Hmark _; discriminate Hmark].
  intros Hmark Hspec. cbv beta iota zeta in Hspec. sys_destruct.
  - errno_is_refusal.
  - match goal with
    | [ Hb : mmap_noreserve_backed_ok _ _ _ = true |- _ ] =>
        rewrite Hb in Hmark; discriminate Hmark
    end.
Qed.

(** ** mremap

    One live eager page at 65536 on a one-page budget, fully spent: a
    grow to two pages is refused; the equal-size answer is not a
    request the budget sees; a shrink releases. *)
Definition mremap_model (lim : Z) : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 lim)
              (init_model [] 0 0 demo_sp lim (demo_input [] IEof)).

Definition mremap_in (old_size new_size : word) : SyscallInput :=
  mkInput 216 [65536; old_size; new_size; 1; 0; 0] (fun _ => None) (fun _ => None).

Example mremap_grow_on_spent_budget_is_budget_refused :
  alloc_budget_refused_b (mremap_in 4096 8192) (mremap_model 4096) = true.
Proof. vm_compute. reflexivity. Qed.

Example mremap_grow_within_budget_is_not_budget_refused :
  alloc_budget_refused_b (mremap_in 4096 8192) (mremap_model 8192) = false.
Proof. vm_compute. reflexivity. Qed.

Example mremap_equal_size_is_not_budget_refused :
  alloc_budget_refused_b (mremap_in 4096 4096) (mremap_model 4096) = false.
Proof. vm_compute. reflexivity. Qed.

Definition mremap_two_page_model (lim : Z) : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 lim)
              (init_model [] 0 0 demo_sp lim (demo_input [] IEof)).

Example mremap_shrink_is_not_budget_refused :
  alloc_budget_refused_b (mremap_in 8192 4096) (mremap_two_page_model 8192) = false.
Proof. vm_compute. reflexivity. Qed.

(** THE MARK IS EXACT ON BOTH CHARGE ORDERS, each on a reachable state.
    The mark fires when no placement fits: in-place growth is not
    admitted AND the move's budget gate, [Mremap.mremap_move_budget_b],
    refuses.  The two charges are ordered neither way on every state;
    the header of [Sys/Mm/Mremap.v] carries the argument, and the two
    states below pin one order each.

    The earlier mark fired when EITHER gate refused.  It is kept here,
    as [mremap_budget_refused_two_gate_b], only to pin that the present
    mark is strictly weaker: it implies the earlier one
    ([mremap_budget_refused_implies_two_gate], below) and is silent on
    [ov_model], where the earlier one fired. *)
Definition mremap_budget_refused_two_gate_b (old old_size new_size flags : word)
    (m : Model) : bool :=
  if negb (Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE) then false
  else if negb (Z.eqb (bv_unsigned old mod page_size) 0) then false
  else if page_align_is0_b new_size then false
  else if page_align_is0_b old_size then false
  else
    let h := m_vmmaps m in
    let old_nZ := page_round_up_Z (bv_unsigned old_size) in
    let new_nZ := page_round_up_Z (bv_unsigned new_size) in
    let old_n := Z_to_bv 64 old_nZ in
    let new_n := Z_to_bv 64 new_nZ in
    if negb (mremap_source_b h old old_n old_nZ
             && mremap_backing_uniform_b m old old_n)
    then false
    else if (new_nZ <=? old_nZ)%Z then false
    else negb (mremap_final_budget_b m old old_n old new_n
               && mremap_move_budget_b m old old_n new_n).

(** IN-PLACE CHARGED MORE: an eager page-sized source at 0x10000, a
    MAP_NORESERVE neighbour at 0x11000 with its first page touched, and
    a budget the pre-state half fills.  A grow of the source over the
    neighbour's first page: the in-place post-state would clear the
    neighbour's lazy metadata under the tail and charge it eagerly,
    past the budget; the in-place resolution is not available anyway
    (the tail is occupied); and a move to a free destination FITS,
    exactly at the budget.  Linux moves and succeeds, and the mark is
    silent.  The earlier two-gate mark fired here and dropped the
    input from every budget premise. *)
Definition ov_model : Model :=
  with_vm_backing [(Z_to_bv 64 0x11000, Z_to_bv 64 8192)] [Z_to_bv 64 0x11000]
    (with_vmmaps (mkVmMaps [] [(0x10000, 4096); (0x11000, 8192)] 0 0 16384)
      (init_model [] 0 0 demo_sp 16384 (demo_input [] IEof))).

Example ov_pre_state_within_budget : vm_backing_within_limit ov_model = true.
Proof. vm_compute. reflexivity. Qed.

Example ov_mark_silent_while_a_move_fits :
  mremap_budget_refused_b 0x10000 4096 12288 1 ov_model = false
  /\ mremap_inplace_grow_b ov_model 0x10000 4096 12288 4096 12288 = false
  /\ mremap_fresh_b ov_model 4096 12288 0x10000 4096 0x100000 12288 = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

Example ov_two_gate_fires_where_the_mark_is_silent :
  mremap_budget_refused_two_gate_b 0x10000 4096 12288 1 ov_model = true
  /\ mremap_budget_refused_b 0x10000 4096 12288 1 ov_model = false.
Proof. split; vm_compute; reflexivity. Qed.

(** The charges behind it: the in-place post-state is over the budget,
    the moved one is exactly at it, and the destination-free charge the
    mark reads is the moved one's. *)
Example ov_charges :
  vm_backing_used (mremap_model_next ov_model 0x10000 4096 0x10000 12288) = 20480%Z
  /\ vm_backing_used (mremap_model_next ov_model 0x10000 4096 0x100000 12288) = 16384%Z
  /\ mremap_move_charge ov_model 0x10000 4096 12288 = 16384%Z.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** IN-PLACE CHARGED LESS: an eager page-sized source at
    0x10000 and a PROT_NONE mapping directly above it at 0x11000 —
    recorded in [vm_maps] AND [vm_noaccess], as the NULL-hint PROT_NONE
    arm of [Mmap.mmap_spec] records it, so the state is a pair of
    ordinary mmaps away from a fresh process — on a budget the source
    alone half fills (the PROT_NONE bytes are subtracted from the backed
    charge).  A grow of the source over the whole neighbour: in-place
    growth is unavailable (the tail meets the neighbour), and the
    in-place post-state is charged no more than the source was, because
    the tail's bytes lie under [vm_noaccess] and [State.vm_backed_maps]
    subtracts them — so a mark stated on that post-state is silent for
    every limit that admitted the pre-state.  A move re-creates the
    whole grown mapping at a fresh destination and is charged every byte
    of it, over the budget, at every such destination: the only
    non-errno resolution is budget-refused.
    The mark fires: in-place growth is not admitted and the move's gate
    refuses.  A mark that read the in-place gate alone would not, and
    [Run.source_within_budget] would hold of an input whose source is
    refused. *)
Definition un_model : Model :=
  with_vmmaps
    (mkVmMapsFull [] [(0x10000, 4096); (0x11000, 8192)] [(0x11000, 8192)]
       0 0 8192 (Z_to_bv 64 0) (Z_to_bv 64 sp_window_lo))
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof)).

Example un_pre_state_within_budget : vm_backing_within_limit un_model = true.
Proof. vm_compute. reflexivity. Qed.

Example un_mark_fires_on_the_move_refusal :
  mremap_budget_refused_b 0x10000 4096 12288 1 un_model = true
  /\ mremap_inplace_grow_b un_model 0x10000 4096 12288 4096 12288 = false
  /\ mremap_fresh_b un_model 4096 12288 0x10000 4096 0x100000 12288 = false.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** The charges behind it: the in-place post-state is within the
    budget, the moved one is over it, and the destination-free charge
    the mark reads is the moved one's. *)
Example un_charges :
  vm_backing_used (mremap_model_next un_model 0x10000 4096 0x10000 12288) = 4096%Z
  /\ vm_backing_used (mremap_model_next un_model 0x10000 4096 0x100000 12288) = 12288%Z
  /\ mremap_move_charge un_model 0x10000 4096 12288 = 12288%Z.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** ...and the in-place gate alone passes on this state, which is the
    silence the witness exposes. *)
Example un_inplace_gate_passes :
  mremap_final_budget_b un_model 0x10000 4096 0x10000 12288 = true.
Proof. vm_compute. reflexivity. Qed.

(** The [region_free] readings the lemmas below need: freeness of an
    appended ledger is freeness of its right half, and freeness survives
    dropping an entry. *)
Lemma region_free_app_r : forall l1 l2 lo n,
  region_free (l1 ++ l2) lo n = true -> region_free l2 lo n = true.
Proof.
  intros l1 l2 lo n H. apply region_free_intro. intros a sz Hin.
  exact (region_free_In _ _ _ _ _ H (in_or_app _ _ _ (or_intror Hin))).
Qed.

Lemma region_free_map_remove : forall maps old lo n,
  region_free maps lo n = true -> region_free (map_remove maps old) lo n = true.
Proof.
  intros maps old lo n H. apply region_free_intro. intros a sz Hin.
  unfold map_remove in Hin. apply List.filter_In in Hin as [Hin _].
  exact (region_free_In _ _ _ _ _ H Hin).
Qed.

(** The rounded request as the spec computes it: page sized, and a word
    whenever [page_align_is0_b] passed it. *)
Lemma page_round_up_Z_mod : forall z, (page_round_up_Z z mod page_size = 0)%Z.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma page_round_up_Z_nonneg : forall z, (0 <= z)%Z -> (0 <= page_round_up_Z z)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  pose proof (Z.div_pos (z + 4096 - 1) 4096 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma page_align_is0_b_false_word : forall len,
  page_align_is0_b len = false ->
  bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
  = page_round_up_Z (bv_unsigned len).
Proof.
  intros len H. unfold page_align_is0_b in H.
  apply orb_false_iff in H as [_ H]. apply Z.leb_gt in H.
  pose proof (bv_unsigned_in_range 64 len) as Hr.
  change (bv_modulus 64) with two_pow_64 in Hr.
  apply mremap_u64. split; [apply page_round_up_Z_nonneg; lia | exact H].
Qed.

(** The limit is carried across the resize unchanged. *)
Lemma mremap_model_next_limit : forall m old old_n dst new_n,
  vm_limit (m_vmmaps (mremap_model_next m old old_n dst new_n))
  = vm_limit (m_vmmaps m).
Proof. reflexivity. Qed.

(** THE RULE, abstract.  On a grow past the mark's own argument gates,
    the mark is exactly "in-place growth not admitted and the move's
    budget gate refusing". *)
Lemma mremap_budget_refused_iff :
  forall old old_size new_size flags m,
  Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE = true ->
  Z.eqb (bv_unsigned old mod page_size) 0 = true ->
  page_align_is0_b new_size = false ->
  (TASK_SIZE <? page_round_up_Z (bv_unsigned new_size))%Z = false ->
  page_align_is0_b old_size = false ->
  mremap_source_b (m_vmmaps m) old
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
    (page_round_up_Z (bv_unsigned old_size))
  && mremap_backing_uniform_b m old
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) = true ->
  (page_round_up_Z (bv_unsigned old_size)
   < page_round_up_Z (bv_unsigned new_size))%Z ->
  mremap_budget_refused_b old old_size new_size flags m
  = negb (mremap_inplace_grow_b m old
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
            (page_round_up_Z (bv_unsigned old_size))
            (page_round_up_Z (bv_unsigned new_size))
          || mremap_move_budget_b m old
               (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
               (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))).
Proof.
  intros old old_size new_size flags m Hflags Halign Hnew Htask Hold Hsrc Hgrow.
  unfold mremap_budget_refused_b. cbv zeta.
  rewrite Hflags, Halign, Hnew, Htask, Hold, Hsrc. cbn [negb].
  rewrite (proj2 (Z.leb_gt _ _) Hgrow). reflexivity.
Qed.

(** What a mark that fires says: every argument gate passed, the
    request grows, in-place growth is not admitted and the move's budget
    gate refuses. *)
Lemma mremap_budget_refused_inv :
  forall old old_size new_size flags m,
  mremap_budget_refused_b old old_size new_size flags m = true ->
  Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE = true
  /\ Z.eqb (bv_unsigned old mod page_size) 0 = true
  /\ page_align_is0_b new_size = false
  /\ (TASK_SIZE <? page_round_up_Z (bv_unsigned new_size))%Z = false
  /\ page_align_is0_b old_size = false
  /\ mremap_source_b (m_vmmaps m) old
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
       (page_round_up_Z (bv_unsigned old_size))
     && mremap_backing_uniform_b m old
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) = true
  /\ (page_round_up_Z (bv_unsigned old_size)
      < page_round_up_Z (bv_unsigned new_size))%Z
  /\ mremap_inplace_grow_b m old
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
       (page_round_up_Z (bv_unsigned old_size))
       (page_round_up_Z (bv_unsigned new_size)) = false
  /\ mremap_move_budget_b m old
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = false.
Proof.
  intros old old_size new_size flags m H.
  unfold mremap_budget_refused_b in H. cbv zeta in H.
  destruct (Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE) eqn:E1;
    cbn [negb] in H; [| discriminate H].
  destruct (Z.eqb (bv_unsigned old mod page_size) 0) eqn:E2;
    cbn [negb] in H; [| discriminate H].
  destruct (page_align_is0_b new_size) eqn:E3; [discriminate H |].
  destruct (TASK_SIZE <? page_round_up_Z (bv_unsigned new_size))%Z eqn:E3b;
    [discriminate H |].
  destruct (page_align_is0_b old_size) eqn:E4; [discriminate H |].
  destruct (mremap_source_b _ _ _ _ && mremap_backing_uniform_b _ _ _) eqn:E5;
    cbn [negb] in H; [| discriminate H].
  destruct (_ <=? _)%Z eqn:E6; [discriminate H |].
  apply Z.leb_gt in E6.
  apply negb_true_iff, orb_false_iff in H as [Hip Hmv].
  exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl
           (conj eq_refl (conj E6 (conj Hip Hmv)))))))).
Qed.

(** SOUNDNESS for the in-place resolution: where the mark fires,
    [Mremap.mremap_inplace_grow_b] is [false].  The mark reads the
    in-place admission directly, so this needs no ledger hypothesis. *)
Lemma mremap_budget_refused_refuses_inplace : forall old old_size new_size flags m,
  mremap_budget_refused_b old old_size new_size flags m = true ->
  mremap_inplace_grow_b m old
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
    (page_round_up_Z (bv_unsigned old_size))
    (page_round_up_Z (bv_unsigned new_size)) = false.
Proof.
  intros old old_size new_size flags m Hmark.
  destruct (mremap_budget_refused_inv _ _ _ _ _ Hmark)
    as (_ & _ & _ & _ & _ & _ & _ & Hip & _).
  exact Hip.
Qed.

(** SOUNDNESS for the moved resolution: where the mark fires, no fresh
    destination that carries no backing metadata is admitted by
    [Mremap.mremap_fresh_b] — its budget conjunct reads, at such a
    destination, the charge [Mremap.mremap_move_budget_b] refused
    ([Mremap.mremap_move_charge_at_fresh]).  The metadata hypotheses
    are instances, at [dst], of the ledger invariants named in
    [Sys/Mm/Mremap.v]'s charge header ([State.noaccess_pages_owned] and
    the reservation-under-live-mapping invariant of the lazy ledgers).
    With [mremap_budget_refused_refuses_inplace]: a marked request has
    no non-errno resolution. *)
Lemma mremap_budget_refused_refuses_move :
  forall old old_size new_size flags m dst,
  (forall (a sz : word), In (a, sz) (map_remove (vm_maps (m_vmmaps m)) old) ->
     (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z) ->
  region_free (vm_noaccess (m_vmmaps m)) dst
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = true ->
  maps_subtract
    (maps_subtract (m_vm_lazy m) (bv_unsigned old)
       (bv_unsigned old
        + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))))
    (bv_unsigned dst)
    (bv_unsigned dst
     + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))))
  = maps_subtract (m_vm_lazy m) (bv_unsigned old)
      (bv_unsigned old
       + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))) ->
  List.filter
    (page_outside_range (bv_unsigned dst)
       (bv_unsigned dst
        + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))))
    (List.filter
       (page_outside_range (bv_unsigned old)
          (bv_unsigned old
           + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))))
       (m_vm_materialized m))
  = List.filter
      (page_outside_range (bv_unsigned old)
         (bv_unsigned old
          + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))))
      (m_vm_materialized m) ->
  mremap_budget_refused_b old old_size new_size flags m = true ->
  mremap_fresh_b m
    (page_round_up_Z (bv_unsigned old_size))
    (page_round_up_Z (bv_unsigned new_size)) old
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = false.
Proof.
  intros old old_size new_size flags m dst Hfit Hnoacc Hlazy Hpages Hmark.
  destruct (mremap_budget_refused_inv _ _ _ _ _ Hmark)
    as (_ & _ & Hnew & _ & _ & _ & Hgrow & _ & Hmv).
  set (old_n := Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) in *.
  set (new_n := Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) in *.
  pose proof (page_align_is0_b_false_word new_size Hnew) as Hnw. fold new_n in Hnw.
  pose proof (page_round_up_Z_mod (bv_unsigned new_size)) as Hnmod.
  pose proof (page_round_up_Z_nonneg (bv_unsigned old_size)
                (proj1 (bv_unsigned_in_range 64 old_size))) as Honn.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  destruct (mremap_fresh_b m _ _ old old_n dst new_n) eqn:Hf; [exfalso | reflexivity].
  unfold mremap_fresh_b in Hf. cbv zeta in Hf.
  rewrite !Bool.andb_true_iff in Hf.
  destruct Hf as (((((_ & Hdalign) & _) & Hdtop) & Hdfree) & Hgate).
  apply Z.eqb_eq in Hdalign. apply Z.leb_le in Hdtop.
  unfold mremap_move_budget_b in Hmv.
  unfold mremap_final_budget_b, vm_backing_within_limit in Hgate.
  rewrite mremap_model_next_limit in Hgate.
  rewrite (mremap_move_charge_at_fresh m old old_n dst new_n) in Hgate;
    [rewrite Hgate in Hmv; discriminate Hmv | exact Hdalign
    | rewrite Hnw; exact Hnmod | rewrite Hnw; lia | rewrite Hnw; lia | exact Hfit
    | apply region_free_map_remove; exact (region_free_app_r _ _ _ _ Hdfree)
    | exact Hnoacc | exact Hlazy | exact Hpages].
Qed.

(** COMPLETENESS against the move: in-place growth not admitted and the
    move's gate refusing at one fresh destination that carries no
    backing metadata fires the mark.  The hypotheses are the mark's
    argument gates, the in-place refusal, and the metadata hypotheses of
    [mremap_budget_refused_refuses_move]. *)
Lemma mremap_budget_refused_fires_on_move_refusal :
  forall old old_size new_size flags m dst,
  Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE = true ->
  Z.eqb (bv_unsigned old mod page_size) 0 = true ->
  page_align_is0_b new_size = false ->
  (TASK_SIZE <? page_round_up_Z (bv_unsigned new_size))%Z = false ->
  page_align_is0_b old_size = false ->
  mremap_source_b (m_vmmaps m) old
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
    (page_round_up_Z (bv_unsigned old_size))
  && mremap_backing_uniform_b m old
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) = true ->
  (page_round_up_Z (bv_unsigned old_size)
   < page_round_up_Z (bv_unsigned new_size))%Z ->
  (* in-place growth is not admitted *)
  mremap_inplace_grow_b m old
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
    (page_round_up_Z (bv_unsigned old_size))
    (page_round_up_Z (bv_unsigned new_size)) = false ->
  (* [dst] is fresh: the non-budget conjuncts of [Mremap.mremap_fresh_b] *)
  (bv_unsigned dst mod page_size = 0)%Z ->
  (bv_unsigned dst + page_round_up_Z (bv_unsigned new_size)
   <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) dst
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = true ->
  (* ...and carries no backing metadata *)
  (forall (a sz : word), In (a, sz) (map_remove (vm_maps (m_vmmaps m)) old) ->
     (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z) ->
  region_free (vm_noaccess (m_vmmaps m)) dst
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = true ->
  maps_subtract
    (maps_subtract (m_vm_lazy m) (bv_unsigned old)
       (bv_unsigned old
        + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))))
    (bv_unsigned dst)
    (bv_unsigned dst
     + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))))
  = maps_subtract (m_vm_lazy m) (bv_unsigned old)
      (bv_unsigned old
       + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))) ->
  List.filter
    (page_outside_range (bv_unsigned dst)
       (bv_unsigned dst
        + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))))
    (List.filter
       (page_outside_range (bv_unsigned old)
          (bv_unsigned old
           + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))))
       (m_vm_materialized m))
  = List.filter
      (page_outside_range (bv_unsigned old)
         (bv_unsigned old
          + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))))
      (m_vm_materialized m) ->
  (* the move's gate refuses at [dst] *)
  mremap_final_budget_b m old
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = false ->
  mremap_budget_refused_b old old_size new_size flags m = true.
Proof.
  intros old old_size new_size flags m dst Hflags Halign Hnew Htask Hold Hsrc Hgrow
    Hip Hdalign Hdtop Hdfree Hfit Hnoacc Hlazy Hpages Hgate.
  rewrite (mremap_budget_refused_iff old old_size new_size flags m
             Hflags Halign Hnew Htask Hold Hsrc Hgrow).
  rewrite Hip. cbn [orb].
  set (old_n := Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) in *.
  set (new_n := Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) in *.
  pose proof (page_align_is0_b_false_word new_size Hnew) as Hnw. fold new_n in Hnw.
  pose proof (page_round_up_Z_mod (bv_unsigned new_size)) as Hnmod.
  pose proof (page_round_up_Z_nonneg (bv_unsigned old_size)
                (proj1 (bv_unsigned_in_range 64 old_size))) as Honn.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  apply negb_true_iff.
  unfold mremap_move_budget_b.
  unfold mremap_final_budget_b, vm_backing_within_limit in Hgate.
  rewrite mremap_model_next_limit in Hgate.
  rewrite (mremap_move_charge_at_fresh m old old_n dst new_n) in Hgate;
    [exact Hgate | exact Hdalign | rewrite Hnw; exact Hnmod
    | rewrite Hnw; lia | rewrite Hnw; lia | exact Hfit
    | apply region_free_map_remove; exact (region_free_app_r _ _ _ _ Hdfree)
    | exact Hnoacc | exact Hlazy | exact Hpages].
Qed.

(** The protected half of "fresh", from the ledger invariant alone.
    [Mremap.mremap_fresh_avoids_noaccess] proves the same conclusion
    but takes the whole of [Mremap.mremap_fresh_b], budget conjunct
    included; its page-granularity argument reads only the alignment of
    [dst], the shape of [new_n] and freeness against
    [vm_reserved ++ vm_maps].  This is that argument on exactly those
    hypotheses, so a consumer can derive the [vm_noaccess] hypothesis of
    [Mremap.mremap_move_charge_at_fresh] BEFORE it knows the gate
    passes. *)
Lemma fresh_dst_avoids_noaccess : forall h dst new_n,
  noaccess_pages_owned h ->
  (0 < bv_unsigned new_n)%Z ->
  (bv_unsigned new_n mod page_size = 0)%Z ->
  (bv_unsigned dst mod page_size = 0)%Z ->
  region_free (vm_reserved h ++ vm_maps h) dst new_n = true ->
  region_free (vm_noaccess h) dst new_n = true.
Proof.
  intros h dst new_n Hown Hpos Hmod Halign Hrf.
  assert (Hhi : ((bv_unsigned dst + bv_unsigned new_n) mod page_size = 0)%Z).
  { rewrite Z.add_mod by (unfold page_size; lia).
    rewrite Halign, Hmod. reflexivity. }
  apply region_free_intro. intros a n Hin.
  destruct (Hown a n Hin) as [Hn Hpage].
  destruct (iv_overlap dst new_n a n) eqn:Hov; [exfalso|reflexivity].
  unfold iv_overlap in Hov.
  apply andb_true_iff in Hov as [Hov1 Hov2].
  apply Z.ltb_lt in Hov1. apply Z.ltb_lt in Hov2.
  remember (Z.max (bv_unsigned dst) (bv_unsigned a)) as x eqn:Hx.
  destruct (Hpage x ltac:(lia)) as [b [s [Hinm [Hb1 Hb2]]]].
  destruct (page_round_down_Z_within (bv_unsigned dst)
              (bv_unsigned dst + bv_unsigned new_n) x Halign Hhi ltac:(lia))
    as [Hf1 Hf2].
  pose proof (region_free_In _ _ _ b s Hrf
                (in_or_app _ _ _ (or_intror Hinm))) as Hno.
  unfold iv_overlap in Hno.
  apply andb_false_iff in Hno as [Hc|Hc]; apply Z.ltb_ge in Hc; lia.
Qed.

(** THE MOVE'S CHARGE ADMITS EVERY FRESH DESTINATION: where the move's
    budget gate [Mremap.mremap_move_budget_b] passes, the gate
    [Mremap.mremap_final_budget_b] that [Mremap.mremap_fresh_b] reads
    passes at every destination that is page aligned, ends at or below
    [alloc_top] and is free against [vm_reserved ++ vm_maps] — the
    non-budget conjuncts of [Mremap.mremap_fresh_b] that bear on the
    charge.  The ledger hypotheses are [State.noaccess_pages_owned], the
    fit of every live mapping other than the source, and the two
    lazy-ledger identities [Mremap.mremap_move_charge_at_fresh] takes;
    the [vm_noaccess] hypothesis of that lemma comes from
    [fresh_dst_avoids_noaccess].  The converse direction of
    [mremap_budget_refused_refuses_move].  The two side conditions on
    [new_n] are what [Mremap.mremap_spec] supplies at the call site: it
    passes [new_n = Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))]
    under [page_align_is0_b new_size = false]. *)
Lemma mremap_move_budget_admits_fresh : forall m old old_n dst new_n,
  (bv_unsigned dst mod page_size = 0)%Z ->
  (bv_unsigned new_n mod page_size = 0)%Z ->
  (0 < bv_unsigned new_n)%Z ->
  (bv_unsigned dst + bv_unsigned new_n <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) dst new_n
  = true ->
  noaccess_pages_owned (m_vmmaps m) ->
  (forall (a sz : word), In (a, sz) (map_remove (vm_maps (m_vmmaps m)) old) ->
     (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z) ->
  maps_subtract
    (maps_subtract (m_vm_lazy m) (bv_unsigned old)
       (bv_unsigned old + bv_unsigned old_n))
    (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n)
  = maps_subtract (m_vm_lazy m) (bv_unsigned old)
      (bv_unsigned old + bv_unsigned old_n) ->
  List.filter (page_outside_range (bv_unsigned dst)
                 (bv_unsigned dst + bv_unsigned new_n))
    (List.filter (page_outside_range (bv_unsigned old)
                    (bv_unsigned old + bv_unsigned old_n))
       (m_vm_materialized m))
  = List.filter (page_outside_range (bv_unsigned old)
                   (bv_unsigned old + bv_unsigned old_n))
      (m_vm_materialized m) ->
  mremap_move_budget_b m old old_n new_n = true ->
  mremap_final_budget_b m old old_n dst new_n = true.
Proof.
  intros m old old_n dst new_n Hdalign Hnmod Hpos Hdtop Hdfree Hown Hfit
    Hlazy Hpages Hmv.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mremap_move_budget_b in Hmv.
  unfold mremap_final_budget_b, vm_backing_within_limit.
  rewrite mremap_model_next_limit.
  rewrite (mremap_move_charge_at_fresh m old old_n dst new_n);
    [exact Hmv | exact Hdalign | exact Hnmod | exact Hpos | lia | exact Hfit
    | apply region_free_map_remove; exact (region_free_app_r _ _ _ _ Hdfree)
    | exact (fresh_dst_avoids_noaccess _ _ _ Hown Hpos Hnmod Hdalign Hdfree)
    | exact Hlazy | exact Hpages].
Qed.

(** The same on a state with empty lazy ledgers ([m_vm_lazy] and
    [m_vm_materialized] both [nil]), where the two lazy-ledger
    identities hold by computation: what is left to cite is
    [State.noaccess_pages_owned] and the fit of the live mappings. *)
Lemma mremap_move_budget_admits_fresh_lazyfree :
  forall m old old_n dst new_n,
  m_vm_lazy m = [] ->
  m_vm_materialized m = [] ->
  (bv_unsigned dst mod page_size = 0)%Z ->
  (bv_unsigned new_n mod page_size = 0)%Z ->
  (0 < bv_unsigned new_n)%Z ->
  (bv_unsigned dst + bv_unsigned new_n <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) dst new_n
  = true ->
  noaccess_pages_owned (m_vmmaps m) ->
  (forall (a sz : word), In (a, sz) (map_remove (vm_maps (m_vmmaps m)) old) ->
     (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z) ->
  mremap_move_budget_b m old old_n new_n = true ->
  mremap_final_budget_b m old old_n dst new_n = true.
Proof.
  intros m old old_n dst new_n Hlz Hmat Hdalign Hnmod Hpos Hdtop Hdfree Hown
    Hfit Hmv.
  apply (mremap_move_budget_admits_fresh m old old_n dst new_n
           Hdalign Hnmod Hpos Hdtop Hdfree Hown Hfit);
    [rewrite Hlz; reflexivity | rewrite Hmat; reflexivity | exact Hmv].
Qed.

(** THE DIRECTION OF THE CHANGE: the mark implies the earlier two-gate
    mark, so every input a budget premise kept under the earlier mark
    it keeps now, and [ov_two_gate_fires_where_the_mark_is_silent]
    shows the converse fails.  The present mark is the weaker one. *)
Lemma mremap_budget_refused_implies_two_gate :
  forall old old_size new_size flags m,
  mremap_budget_refused_b old old_size new_size flags m = true ->
  mremap_budget_refused_two_gate_b old old_size new_size flags m = true.
Proof.
  intros old old_size new_size flags m Hmark.
  destruct (mremap_budget_refused_inv _ _ _ _ _ Hmark)
    as (E1 & E2 & E3 & _ & E4 & E5 & Hgrow & _ & Hmv).
  unfold mremap_budget_refused_two_gate_b. cbv zeta.
  rewrite E1, E2, E3, E4, E5. cbn [negb].
  rewrite (proj2 (Z.leb_gt _ _) Hgrow).
  rewrite Hmv, andb_false_r. reflexivity.
Qed.

(** ** mprotect

    The reserve-then-commit idiom: a PROT_NONE page inside a live
    mapping, exposed rw.  On a spent budget the exposure is refused;
    with a page left it is not; exposing an already-rw page charges
    nothing. *)
Definition mprotect_in (addr len prot : word) : SyscallInput :=
  mkInput 226 [addr; len; prot; 0; 0; 0] (fun _ => None) (fun _ => None).

Example mprotect_expose_on_spent_budget_is_budget_refused :
  alloc_budget_refused_b (mprotect_in 65536 4096 3) (fixed_rw_model 0) = true.
Proof. vm_compute. reflexivity. Qed.

Example mprotect_expose_within_budget_is_not_budget_refused :
  alloc_budget_refused_b (mprotect_in 65536 4096 3) (fixed_rw_model 4096) = false.
Proof. vm_compute. reflexivity. Qed.

Example mprotect_already_rw_is_not_budget_refused :
  alloc_budget_refused_b (mprotect_in 65536 4096 3) (mremap_model 4096) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma mprotect_dispatch : forall i m o,
  bv_unsigned (in_sysno i) = 226%Z ->
  syscall_spec i m o
  <-> mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Ltac mprotect_errno_is_refusal :=
  match goal with
  | [ Hin : In ?e mprotect_errnos |- _ ] =>
      destruct Hin as [<- | []]; vm_compute; reflexivity
  end.

(** SOUNDNESS over the whole arm, abstract. *)
Lemma mprotect_budget_refused_is_refusal : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 226%Z ->
  alloc_budget_refused_b i m = true ->
  syscall_spec i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m eff m' evs E Hmark Hspec.
  unfold alloc_budget_refused_b in Hmark. rewrite E in Hmark.
  cbn [Z.eqb Pos.eqb] in Hmark.
  apply (proj1 (mprotect_dispatch i m _ E)) in Hspec.
  unfold refusal_b. rewrite E. cbv zeta.
  assert (Hne : (226 =? 214)%Z = false) by reflexivity. rewrite Hne.
  assert (Harm : injected_arm 226 = Some (mkInjectedArm 226 FamAlloc mprotect_errnos))
    by reflexivity.
  rewrite Harm. cbn [ia_errnos].
  unfold mprotect_budget_refused_b in Hmark. unfold mprotect_spec in Hspec.
  revert Hmark Hspec.
  destruct (mprotect_grows_conflict_b (in_arg i 2)); [intros Hmark; discriminate Hmark |].
  destruct (negb (Z.eqb (bv_unsigned (in_arg i 0) mod page_size) 0));
    [intros Hmark; discriminate Hmark |].
  destruct (w_is0 (in_arg i 1)); [intros Hmark; discriminate Hmark |].
  destruct (two_pow_64 <=? bv_unsigned (in_arg i 0)
                         + page_round_up_Z (bv_unsigned (in_arg i 1)))%Z;
    [intros Hmark; discriminate Hmark |].
  destruct (mprotect_modeled_b (in_arg i 2)); [| intros Hmark; discriminate Hmark].
  cbv zeta. intros Hmark Hspec.
  unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, get_model, modify
    in Hspec.
  cbv beta zeta in Hspec. sys_destruct.
  match goal with
  | [ H : ?f i m (Ok eff m' ?e) |- _ ] => revert H
  end.
  revert Hmark.
  destruct (map_contains (vm_noaccess (m_vmmaps m)) (in_arg i 0)
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))
            && map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))));
    [| intros Hmark _; discriminate Hmark].
  intros Hmark Hspec. cbv beta iota zeta in Hspec. sys_destruct.
  - mprotect_errno_is_refusal.
  - match goal with
    | [ Hb : mprotect_budget_ok _ _ _ = true |- _ ] =>
        rewrite Hb in Hmark; discriminate Hmark
    end.
Qed.

(* =========================================================================
   PART 2 — the first-touch clauses
   ========================================================================= *)

(** ** An instruction that touches a lazy page

    One instruction at 0x100, [sd x0, 0(a0)] (0x00053023), with [a0]
    pointing at a page that is writable in the machine and recorded
    LAZY in the model — a MAP_NORESERVE grant the process has not yet
    touched.  The machine state is built by hand so that its memory is
    a small function rather than an entry stack image. *)
Definition touch_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 4;
  seg_perms := "r-x"%string;
  seg_bytes := ["23300500"%pstring]
|}.
Definition touch_segments : list Segment := [touch_segment].
Definition touch_page : Z := 0x10000%Z.

Definition touch_ms : machine_state := {|
  ms_regs := bvmap_set 10 (Z_to_bv 64 touch_page) bvmap_empty;
  ms_fregs := bvmap_empty;
  ms_pc_val := Z_to_bv 64 0x100;
  ms_svc_pending := None;
  ms_resv := None; ms_fcsr := Z_to_bv 32 0;
  ms_mem := fun a =>
    if ((touch_page <=? bv_unsigned a) && (bv_unsigned a <? touch_page + page_size))%Z
    then Some (Z_to_bv 8 0) else None;
  ms_rom := fun addr =>
    match memory_read touch_segments addr 1 with
    | Some (b :: _) => Some b
    | _ => None
    end |}.

(** The model: the page is a lazy reservation and nothing is charged
    yet, at budget [lim].  SYNTHETIC — the lazy range has no [vm_maps]
    entry, which no grant produces; the state exercises clause A of the
    mark, not the allocator. *)
Definition touch_model (lim : Z) : Model :=
  with_vm_backing [(Z_to_bv 64 touch_page, Z_to_bv 64 page_size)] []
    (init_model (segments_reserved touch_segments) 0 0 demo_sp lim (demo_input [] IEof)).

(** The interpreter reports the store as a successful eight-byte access
    of the page — a scalar, so [vm_compute] never builds the successor
    state. *)
Definition touch_accesses : option (list memory_access) :=
  match RiscvSemantics.step_accesses touch_segments touch_ms with
  | MachineOk r => Some (@accessed_ranges _ r)
  | MachineFault | MachineUnmodeled => None
  end.

Example touch_store_reports_the_page :
  touch_accesses = Some [(Z_to_bv 64 touch_page, 8%nat)].
Proof. check_eq. Qed.

(** With the budget spent (zero), the touch is budget-refused ... *)
Example touch_on_spent_budget_is_budget_refused :
  budget_refused_at touch_segments (mkCfg touch_ms (touch_model 0)).
Proof.
  split; [vm_compute; reflexivity |]. left. split; [reflexivity |].
  pose proof touch_store_reports_the_page as H. unfold touch_accesses in H.
  destruct (RiscvSemantics.step_accesses touch_segments touch_ms) as [r | |] eqn:E;
    try discriminate H.
  exists r. split; [cbn [cfg_ms]; exact E |].
  injection H as Hr. cbn [cfg_model]. rewrite Hr. vm_compute. reflexivity.
Qed.

(** ... and IS the error transition. *)
Example touch_on_spent_budget_errors :
  sstep touch_segments (mkCfg touch_ms (touch_model 0)) [] SError.
Proof.
  pose proof touch_store_reports_the_page as H. unfold touch_accesses in H.
  destruct (RiscvSemantics.step_accesses touch_segments touch_ms) as [r | |] eqn:E;
    try discriminate H.
  injection H as Hr.
  apply budget_fault_instr_sstep_error with (report := r);
    [vm_compute; reflexivity | reflexivity | exact E |].
  rewrite Hr. vm_compute. reflexivity.
Qed.

(** With a page of budget left the same touch is NOT budget-refused. *)
Example touch_within_budget_is_not_budget_refused :
  ~ budget_refused_at touch_segments (mkCfg touch_ms (touch_model page_size)).
Proof.
  intros (_ & [(_ & r & E & Hmat) | (x8 & Hx8 & _)]); cbn [cfg_ms cfg_model] in *.
  - pose proof touch_store_reports_the_page as H. unfold touch_accesses in H.
    rewrite E in H. injection H as Hr. rewrite Hr in Hmat.
    vm_compute in Hmat. discriminate Hmat.
  - discriminate Hx8.
Qed.

(** A fault the interpreter raises for ITS OWN reasons is not a budget
    refusal: [Checks.Omni.ebreak_ms] faults ([Checks.Omni.ebreak_faults])
    and takes the same [SError] transition, and the mark is false on it
    at every budget. *)
Example ebreak_fault_is_not_budget_refused : forall lim,
  ~ budget_refused_at ebreak_segments (mkCfg ebreak_ms (ebreak_model lim)).
Proof.
  intros lim (_ & [(_ & r & E & _) | (x8 & Hx8 & _)]); cbn [cfg_ms cfg_model] in *.
  - pose proof (drop_step_accesses ebreak_segments ebreak_ms) as Hd.
    rewrite E, ebreak_faults in Hd. discriminate Hd.
  - assert (Hnone : ms_svc_pending ebreak_ms = None) by reflexivity.
    congruence.
Qed.

(** ** A syscall whose copy-in touches a lazy page

    [write(1, 0x1000, 1)] from a process whose lazy reservation covers
    the first two pages, page 0 already charged, budget one page: the
    copy-in of the byte at 0x1000 would charge a second page.  The
    checker accepts the write, and the materialization of its effect
    fails — the effect clause of the mark. *)
Definition wtouch_ms : machine_state := {|
  ms_regs := bvmap_set 10 (Z_to_bv 64 1)
               (bvmap_set 11 (Z_to_bv 64 0x1000)
                  (bvmap_set 12 (Z_to_bv 64 1) bvmap_empty));
  ms_fregs := bvmap_empty;
  ms_pc_val := Z_to_bv 64 0x100;
  ms_svc_pending := Some (Z_to_bv 64 64);
  ms_resv := None; ms_fcsr := Z_to_bv 32 0;
  ms_mem := fun a => if bv_eqb a (Z_to_bv 64 0x1000) then Some (Z_to_bv 8 0) else None;
  ms_rom := fun _ => None |}.

Definition wtouch_model : Model :=
  with_vm_backing [(0, 0x2000)] [0]
    (init_model [] 0 0 demo_sp 0x1000 (demo_input [] IEof)).

Definition wtouch_eff : SyscallEffect :=
  mkEffectU 1 [] [] [] [] [(Z_to_bv 64 0x1000, 1%nat)].

Example wtouch_checker :
  check_syscall (sys_input [] wtouch_ms (Z_to_bv 64 64)) wtouch_eff wtouch_model
  = CheckOk wtouch_model [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 0)].
Proof. check_eq. Qed.

Example wtouch_is_budget_refused :
  budget_refused_at [] (mkCfg wtouch_ms wtouch_model).
Proof.
  split; [vm_compute; reflexivity |]. right.
  exists (Z_to_bv 64 64). split; [reflexivity |]. right.
  exists wtouch_eff, wtouch_model, [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 0)].
  split; [apply check_syscall_sound_ok; exact wtouch_checker |].
  split; [vm_compute; reflexivity |].
  vm_compute. reflexivity.
Qed.

Example wtouch_errors :
  sstep [] (mkCfg wtouch_ms wtouch_model) [] SError.
Proof.
  eapply budget_fault_syscall_sstep_error;
    [ vm_compute; reflexivity
    | reflexivity
    | apply check_syscall_sound_ok; exact wtouch_checker
    | vm_compute; reflexivity
    | vm_compute; reflexivity ].
Qed.

(* =========================================================================
   PART 3 — the dispatcher: every allocation arm and nothing else
   ========================================================================= *)

Example brk_dispatches_to_its_mark :
  alloc_budget_refused_b (brk_in 73728) m_tight_brk = true.
Proof. vm_compute. reflexivity. Qed.

(** A syscall with no allocation arm is never budget-refused, whatever
    its state: [getcwd] ([Checks.SpuriousCfg.getcwd_i]) and the two exit
    numbers; and, off the whole list, [Run.alloc_budget_refused_b_outside].
    [Run.alloc_family_dispatched] is the other half — every [FamAlloc]
    number IS on the list — instantiated here on each arm the table
    registers. *)
Example brk_is_dispatched : In 214%Z alloc_mark_sysnos.
Proof. apply (alloc_family_dispatched 214 (mkInjectedArm 214 FamAlloc [])); reflexivity. Qed.

Example mremap_is_dispatched : In 216%Z alloc_mark_sysnos.
Proof.
  apply (alloc_family_dispatched 216 (mkInjectedArm 216 FamAlloc mremap_errnos));
    reflexivity.
Qed.

Example mmap_is_dispatched : In 222%Z alloc_mark_sysnos.
Proof.
  apply (alloc_family_dispatched 222 (mkInjectedArm 222 FamAlloc mmap_errnos));
    reflexivity.
Qed.

Example mprotect_is_dispatched : In 226%Z alloc_mark_sysnos.
Proof.
  apply (alloc_family_dispatched 226 (mkInjectedArm 226 FamAlloc mprotect_errnos));
    reflexivity.
Qed.

(** Each number on the list reaches its arm's mark:
    [Run.alloc_mark_sysnos_dispatched], instantiated on the brk number. *)
Example brk_number_reaches_its_mark : forall i m,
  bv_unsigned (in_sysno i) = 214%Z ->
  alloc_budget_refused_b i m = brk_budget_refused_b m (in_arg i 0).
Proof. intros i m E. exact (proj1 (alloc_mark_sysnos_dispatched i m) E). Qed.

(** A syscall with no allocation arm is never budget-refused, whatever
    its state: [getcwd] ([Checks.SpuriousCfg.getcwd_i]) and the two exit
    numbers, instances of [Run.alloc_budget_refused_b_outside]. *)
Example getcwd_is_never_budget_refused : forall m,
  alloc_budget_refused_b getcwd_i m = false.
Proof. intros m. reflexivity. Qed.

Example exit_is_never_budget_refused : forall i m,
  exit_sysno (in_sysno i) -> alloc_budget_refused_b i m = false.
Proof.
  intros i m [E | E]; unfold alloc_budget_refused_b; rewrite E; reflexivity.
Qed.

(* =========================================================================
   PART 4 — run level
   ========================================================================= *)

(** ** The reflective evaluator discharges the premise

    [Checks.Examples.exits_c] accepts a straight-line program that ends
    in an exit; such a program never reaches the mark: its instruction
    steps are function answers on a model with no lazy mapping, and its
    one ecall is an exit, which is not an allocation and whose every
    outcome halts.  The same induction as
    [Checks.Examples.exits_c_must_exit_at]. *)
Lemma exits_c_no_budget_refused : forall segs code fuel ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  exits_c segs code fuel ms = true ->
  ~ reaches_budget_refused segs (mkCfg ms model).
Proof.
  intros segs code fuel. induction fuel as [|fuel IH];
    intros ms model Hh Hlazy Hc (tr & c & Hstar & Hb); [discriminate|].
  cbn [exits_c] in Hc.
  destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
  - (* the terminating ecall *)
    apply andb_true_iff in Hc as [Hx8 _].
    assert (Hno : exit_sysno (in_sysno (sys_input segs ms x8))).
    { cbn [in_sysno sys_input].
      apply orb_true_iff in Hx8. destruct Hx8 as [H|H]; apply Z.eqb_eq in H;
        [left|right]; exact H. }
    inversion Hstar as [c0 Heq | c1 evs c2 tr' c3 Hss Hstar']; subst.
    + (* zero steps: the ecall configuration is not budget-refused *)
      destruct Hb as (_ & [(Hnone & _) | (y8 & Hy8 & [Hmark | (eff & m' & evs & Hspec & Hh' & _)])]);
        cbn [cfg_ms cfg_model] in *.
      * congruence.
      * rewrite Hsvc in Hy8. injection Hy8 as <-.
        rewrite (exit_is_never_budget_refused _ _ Hno) in Hmark. discriminate Hmark.
      * rewrite Hsvc in Hy8. injection Hy8 as <-.
        rewrite (exit_dispatch_halts _ _ _ _ _ Hno Hspec) in Hh'. discriminate Hh'.
    + (* one step: only the exit transition, into a halted configuration *)
      inversion Hss; subst; try congruence; unify_svc x8.
      * (* an ordinary syscall step: its post-model would have to run on *)
        match goal with
        | [ H : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
            pose proof (exit_dispatch_halts _ _ _ _ _ Hno H) as Hhalts
        end.
        congruence.
      * (* the exit transition *)
        match goal with
        | [ H : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
            pose proof (exit_dispatch_halts _ _ _ _ _ Hno H) as Hhalts
        end.
        inversion Hstar'; subst.
        -- destruct Hb as (Hb0 & _). cbn [cfg_model] in Hb0. congruence.
        -- match goal with
           | [ H : sstep _ (mkCfg ms _) _ (SNext _) |- _ ] =>
               inversion H; subst; congruence
           end.
      * (* the kill transition: an exit's post-model is not a killed one *)
        exfalso.
        match goal with
        | [ H : syscall_spec _ _ (Ok _ ?m' _), Hk : m_killed ?m' = Some _ |- _ ] =>
            rewrite (exit_dispatch_not_killed _ _ _ _ _ Hno H) in Hk;
            discriminate
        end.
  - (* an ordinary instruction *)
    destruct (RiscvSemantics.step segs ms) as [ms'| |] eqn:Hstep;
      [|discriminate|discriminate].
    inversion Hstar as [c0 Heq | c1 evs c2 tr' c3 Hss Hstar']; subst.
    + exact (budget_refused_at_no_lazy_instr segs ms model Hlazy Hsvc Hb).
    + destruct (sstep_instr_only segs ms model ms' Hlazy Hsvc Hstep _ _ Hss) as [_ Hc2].
      injection Hc2 as ->.
      apply (IH ms' model Hh Hlazy Hc). exists tr', c. split; assumption.
Qed.

(** The exit-0 image satisfies the premise at EVERY budget, entry and
    input: [Checks.Omni.exit0_exits_c] holds at every placement, and the
    initial model has no lazy mapping. *)
Lemma exit0_never_budget_refused : forall lim en inp,
  ~ run_budget_refused exit0_image lim en inp.
Proof.
  intros lim [sp brk0 mbase rnd] inp.
  unfold run_budget_refused, exit0_image, init_config.
  apply exits_c_no_budget_refused with (code := verdict_accept) (fuel := 8%nat);
    [reflexivity | reflexivity | apply exit0_exits_c].
Qed.

Lemma exit0_source_within_budget : forall lim en inp,
  source_within_budget lim exit0_image en inp.
Proof. intros lim en inp. exact (exit0_never_budget_refused lim en inp). Qed.

(** ** The premise bites: a run that reaches the mark

    Six instructions at 0x100 — [addi a7, x0, 222; lui a1, 2; addi a2,
    x0, 3; addi a3, x0, 34; addi a4, x0, -1; ecall] — an
    [mmap(0, 8192, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0)]
    ([a0] and [a5] are zero at entry).  Run at a ONE-PAGE budget the
    request is refused for budget at the ecall, so the run reaches the
    mark: [run_budget_refused] is inhabited and the premise excludes
    this run.  Stepped as [Checks.Omni]'s write-then-loop image is, with
    the memory abstracted: no instruction here touches memory. *)
Definition mm_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 24;
  seg_perms := "r-x"%string;
  seg_bytes := ["9308e00db725000013063000930620021307f0ff73000000"%pstring]
|}.
Definition mm_segments : list Segment := [mm_segment].
Definition mm_image : Image := mkImage mm_segments 0x100 demo_phdrs.

Definition mm_budget : Z := page_size.

Definition mm_ms0 : machine_state :=
  init_machine_state mm_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    demo_draw
    (in_argv demo_proc_input) (in_envp demo_proc_input) (in_uid demo_proc_input)
    (in_hwcap demo_proc_input).
Definition mm_msk (k : nat) : machine_state :=
  match run_steps k mm_segments mm_ms0 with
  | Some ms => ms
  | None => mm_ms0
  end.
Definition mm_s (k : nat) : machine_state := with_mem (mm_msk k) (ms_mem mm_ms0).

Definition mm_model : Model :=
  init_model (segments_reserved mm_segments) (Z_to_bv 64 0x1000)
    (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000) mm_budget demo_proc_input.
Definition mm_c : config := mkCfg (mm_s 0) mm_model.

Lemma mm_config :
  init_config mm_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw mm_budget demo_proc_input
  = mm_c.
Proof. unfold init_config, mm_c. f_equal; try exact (with_mem_eta mm_ms0). Qed.

Lemma mm_step : forall k, (k < 6)%nat -> forall mem,
  RiscvSemantics.step mm_segments (with_mem (mm_msk k) mem)
  = MachineOk (with_mem (mm_msk (S k)) mem).
Proof.
  intros k Hk mem.
  do 6 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
Qed.

Lemma mm_instr_sstep : forall k, (k < 6)%nat ->
  sstep mm_segments (mkCfg (mm_s k) mm_model) []
    (SNext (mkCfg (mm_s (S k)) mm_model)).
Proof.
  intros k Hk. unfold mm_s.
  apply sstep_instr; [reflexivity | |].
  - do 6 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
  - no_lazy. rewrite (mm_step k Hk). reflexivity.
Qed.

Lemma mm_svc6 : ms_svc_pending (mm_s 6) = Some (Z_to_bv 64 222).
Proof. vm_compute. first [reflexivity | f_equal; apply bv_eq; reflexivity]. Qed.

Lemma mm_star : star mm_segments mm_c [] (mkCfg (mm_s 6) mm_model).
Proof.
  change (@nil event) with ((@nil event) ++ ((@nil event) ++ ((@nil event) ++ ((@nil event) ++ ((@nil event) ++ ((@nil event) ++ (@nil event))))))).
  unfold mm_c.
  eapply star_step; [exact (mm_instr_sstep 0 ltac:(lia)) |].
  eapply star_step; [exact (mm_instr_sstep 1 ltac:(lia)) |].
  eapply star_step; [exact (mm_instr_sstep 2 ltac:(lia)) |].
  eapply star_step; [exact (mm_instr_sstep 3 ltac:(lia)) |].
  eapply star_step; [exact (mm_instr_sstep 4 ltac:(lia)) |].
  eapply star_step; [exact (mm_instr_sstep 5 ltac:(lia)) |].
  apply star_refl.
Qed.

(** At the ecall the mark fires: the grant clause, by computation. *)
Lemma mm_ecall_is_budget_refused :
  budget_refused_at mm_segments (mkCfg (mm_s 6) mm_model).
Proof.
  split; [reflexivity |]. right.
  exists (Z_to_bv 64 222). split; [exact mm_svc6 |]. left.
  vm_compute. reflexivity.
Qed.

Theorem mm_run_budget_refused :
  run_budget_refused mm_image mm_budget demo_entry demo_proc_input.
Proof.
  change (reaches_budget_refused mm_segments
            (init_config mm_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
               (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw mm_budget
               demo_proc_input)).
  rewrite mm_config.
  eapply reaches_budget_refused_star; [exact mm_star |].
  apply reaches_budget_refused_intro. exact mm_ecall_is_budget_refused.
Qed.

(** ... so the premise excludes it: the budget family is not the
    constant-pinned family under another name. *)
Theorem mm_not_within_budget :
  ~ source_within_budget mm_budget mm_image demo_entry demo_proc_input.
Proof. intros H. exact (H mm_run_budget_refused). Qed.

(** ** The sealed ascription

    The exit-0 pair satisfies the error-free budget statement at EVERY
    pair of budgets — the image never touches the heap — and so seals
    [Equivalence.SPEC_ERROR_FREE_BUDGETS] under the shipped budgets,
    which is the ascription a generated Checker makes for a flavour
    pair. *)
Theorem exit0_strong_universal_error_free_budgets : forall lim_source lim_target,
  strong_universal_error_free_T_budgets lim_source lim_target exit0_image exit0_image.
Proof.
  intros ls lt [sps brks mbs rnds] [spt brkt mbt rndt] inp _ _ _ _.
  unfold strong_equiv_error_free_budgets.
  split; [| split].
  - apply error_free_iff. cbn [omni_corun exit0_image img_segments].
    apply exit0_never_errors.
  - apply error_free_iff. cbn [omni_corun exit0_image img_segments].
    apply exit0_never_errors.
  - intros tr. cbn [run exit0_image bh_traces].
    rewrite !exit0_obs. reflexivity.
Qed.

Module Exit0BudgetsChecked <: SPEC_ERROR_FREE_BUDGETS ShippedBudgets Exit0Image Exit0Image.
  Definition strong_universal_error_free :=
    exit0_strong_universal_error_free_budgets
      ShippedBudgets.lim_source ShippedBudgets.lim_target.
End Exit0BudgetsChecked.

(** The abort twin: the exit-0 image is never killed — its trace set is
    the prefixes of one exit event — so it is [error_free_unkilled] at
    every budget, and the abort-declared statement holds of the pair. *)
Lemma exit0_never_dies_by_signal : forall lim en inp,
  ~ dies_by_signal (run exit0_image lim en inp).
Proof.
  intros lim [sp brk0 mbase rnd] inp (tr & sig & fs & Htr & Hin).
  cbn [run exit0_image bh_traces] in Htr. apply exit0_obs in Htr.
  destruct tr as [| e tr']; [exact Hin |].
  destruct Htr as [-> Htr']. destruct tr' as [| e' tr'']; [| destruct Htr'].
  destruct Hin as [Hin | []]. discriminate Hin.
Qed.

Theorem exit0_strong_universal_error_free_budgets_abort : forall lim_source lim_target,
  strong_universal_error_free_T_budgets_abort lim_source lim_target exit0_image exit0_image.
Proof.
  intros ls lt [sps brks mbs rnds] [spt brkt mbt rndt] inp _ _ _ _.
  unfold strong_equiv_error_free_budgets_abort, error_free_unkilled.
  split; [| split].
  - split; [| apply exit0_never_dies_by_signal].
    apply error_free_iff. cbn [omni_corun exit0_image img_segments].
    apply exit0_never_errors.
  - split; [| apply exit0_never_dies_by_signal].
    apply error_free_iff. cbn [omni_corun exit0_image img_segments].
    apply exit0_never_errors.
  - intros tr. cbn [run exit0_image bh_traces].
    rewrite !exit0_obs. reflexivity.
Qed.

Module Exit0BudgetsAbortChecked
  <: SPEC_ERROR_FREE_BUDGETS_ABORT ShippedBudgets Exit0Image Exit0Image.
  Definition strong_universal_error_free :=
    exit0_strong_universal_error_free_budgets_abort
      ShippedBudgets.lim_source ShippedBudgets.lim_target.
End Exit0BudgetsAbortChecked.

(** And the constant-pinned error-free statement, where one is proved,
    hands over the budget one at the shipped constants without a new
    proof ([Equivalence.strong_universal_error_free_T_budgets_of_pinned]). *)
Example exit0_budgets_from_pinned :
  strong_universal_error_free_T exit0_image exit0_image ->
  strong_universal_error_free_T_budgets source_alloc_limit target_alloc_limit
    exit0_image exit0_image.
Proof. apply strong_universal_error_free_T_budgets_of_pinned. Qed.

(* =========================================================================
   PART 5 — the configured family and the either pair, on the exit-0 pair
   ========================================================================= *)

(** ** The exit-0 image under a configuration

    Its run has no injected arm to filter — instruction steps and one
    exit — so its trace set under any configuration is the trace set
    under none: the prefixes of the one exit event.  The (->) half is
    the filter being a subset ([Run.obs_trace_cfg_sub]); the (<-) half
    realises the exit through [Checks.SpuriousCfg.exits_c_must_exit_at_cfg]
    and [MustExit.must_exit_at_cfg_realizes]. *)
Lemma exit0_must_exit_at_cfg : forall cfg sp brk0 mbase rnd lim inp,
  must_exit_at_cfg cfg exit0_segments verdict_accept
    (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp).
Proof.
  intros. unfold init_config.
  apply (exits_c_must_exit_at_cfg _ _ _ 8); [reflexivity | reflexivity | apply exit0_exits_c].
Qed.

Lemma exit0_obs_cfg : forall cfg sp brk0 mbase rnd lim inp tr,
  obs_trace_cfg exit0_segments cfg
    (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp) tr
  <-> is_prefix tr [ExitEv verdict_accept (in_fs inp)].
Proof.
  intros cfg sp brk0 mbase rnd lim inp tr. split.
  - intros H.
    exact (proj1 (exit0_obs _ _ _ _ _ _ _) (obs_trace_cfg_sub exit0_segments cfg _ _ H)).
  - intros Hp.
    destruct (must_exit_at_cfg_realizes _ _ _ _
                (exit0_must_exit_at_cfg cfg sp brk0 mbase rnd lim inp) eq_refl)
      as (tr0 & fs & c' & Hstar & _).
    assert (Hfull : obs_trace_cfg exit0_segments cfg
                      (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp)
                      (tr0 ++ [ExitEv verdict_accept fs])).
    { exists (tr0 ++ [ExitEv verdict_accept fs]), c'.
      split; [exact Hstar | apply is_prefix_refl]. }
    pose proof (proj1 (exit0_obs _ _ _ _ _ _ _)
                  (obs_trace_cfg_sub exit0_segments cfg _ _ Hfull)) as Hpre.
    clear Hfull. rename Hpre into Hfull.
    destruct tr0 as [| e tr0'].
    + cbn in Hfull. destruct Hfull as [Heq _]. injection Heq as Hfs. subst fs.
      destruct tr as [| e tr'].
      * exists [], (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp).
        split; [apply star_cfg_refl | exact I].
      * destruct Hp as [-> Hp']. destruct tr' as [| e' tr'']; [| destruct Hp'].
        exists [ExitEv verdict_accept (in_fs inp)], c'.
        split; [exact Hstar | apply is_prefix_refl].
    + cbn in Hfull. destruct Hfull as [_ Hfull].
      destruct tr0'; cbn in Hfull; destruct Hfull.
Qed.

(** The configured error-free budget statement holds of the exit-0 pair
    at EVERY configuration and EVERY pair of budgets ... *)
Theorem exit0_strong_universal_error_free_budgets_scfg : forall cfg lim_source lim_target,
  strong_universal_error_free_T_scfg_budgets cfg lim_source lim_target exit0_image exit0_image.
Proof.
  intros cfg ls lt [sps brks mbs rnds] [spt brkt mbt rndt] inp _ _ _ _.
  unfold strong_equiv_error_free_budgets_scfg.
  split; [| split].
  - apply error_free_scfg_of_error_free.
    apply error_free_iff. cbn [omni_corun exit0_image img_segments].
    apply exit0_never_errors.
  - apply error_free_scfg_of_error_free.
    apply error_free_iff. cbn [omni_corun exit0_image img_segments].
    apply exit0_never_errors.
  - intros tr. cbn [run_scfg exit0_image bh_traces].
    rewrite !exit0_obs_cfg. reflexivity.
Qed.

(** ... and seals the configured surfaces under the shipped budgets
    at the forced-only reading (at may-fail they are the [SpecBudgets]
    surfaces by [Equivalence.strong_universal_error_free_T_scfg_budgets_may_fail]). *)
Module ForcedOnlyCfg <: SPURIOUS_CFG.
  Definition cfg : SpuriousCfg := forced_only_cfg.
End ForcedOnlyCfg.

Module Exit0ScfgBudgetsChecked
  <: SPEC_ERROR_FREE_SCFG_BUDGETS ForcedOnlyCfg ShippedBudgets Exit0Image Exit0Image.
  Definition strong_universal_error_free :=
    exit0_strong_universal_error_free_budgets_scfg ForcedOnlyCfg.cfg
      ShippedBudgets.lim_source ShippedBudgets.lim_target.
End Exit0ScfgBudgetsChecked.

Module Exit0ScfgBudgetsBaselineChecked
  <: SPEC_SCFG_BUDGETS ForcedOnlyCfg ShippedBudgets Exit0Image Exit0Image.
  Definition strong_universal :=
    strong_universal_error_free_T_scfg_budgets_implies _ _ _ _ _
      Exit0ScfgBudgetsChecked.strong_universal_error_free.
End Exit0ScfgBudgetsBaselineChecked.

(** The unfiltered premise reaches the configured statement: what
    [exits_c_no_budget_refused] discharges is enough for every
    configuration. *)
Example exit0_source_within_budget_scfg : forall cfg lim en inp,
  source_within_budget_scfg cfg lim exit0_image en inp.
Proof.
  intros cfg lim en inp.
  apply source_within_budget_scfg_of_source_within_budget.
  exact (exit0_source_within_budget lim en inp).
Qed.

(** ** Neither stance pinned: the exit-0 pair under both readings. *)
Module Exit0BudgetsEitherChecked
  <: SPEC_ERROR_FREE_BUDGETS_EITHER ShippedBudgets Exit0Image Exit0Image.
  Definition strong_universal_error_free :=
    conj (exit0_strong_universal_error_free_budgets
            ShippedBudgets.lim_source ShippedBudgets.lim_target)
         (exit0_strong_universal_error_free_budgets_abort
            ShippedBudgets.lim_source ShippedBudgets.lim_target).
End Exit0BudgetsEitherChecked.

Module Exit0BudgetsEitherBaselineChecked
  <: SPEC_BUDGETS_EITHER ShippedBudgets Exit0Image Exit0Image.
  Definition strong_universal :=
    strong_universal_error_free_T_budgets_either_implies _ _ _ _
      Exit0BudgetsEitherChecked.strong_universal_error_free.
End Exit0BudgetsEitherBaselineChecked.

(** ** The mark and the filter agree

    A configuration removes a refusal only where a non-refusal is also
    admitted ([Run.spurious_refusal_cfg]).  Where the mark fires, every
    admitted outcome IS a refusal (the soundness lemmas of PART 1), so
    nothing at that configuration is spurious and the configured step
    relation admits exactly the unfiltered steps: the mark is about a
    step no configuration can remove.  Stated for the arms whose
    soundness lemma covers the whole arm on every state.  mremap's
    covers it only on states satisfying the ledger hypotheses of
    [mremap_budget_refused_refuses_move] at the destination.  The
    protected-ledger and fit halves are proved invariants
    ([Checks/NoaccessOwned.v], [Checks/MapsFit.v]); the lazy-ledger half
    (no reservation and no materialized page at a fresh destination) is
    not, so mremap is left out here.  On a state whose lazy ledgers are
    empty the whole arm is covered ([Checks/BudgetPremiseMremap.v],
    [mremap_budget_refused_is_refusal_sys_inv]). *)
Lemma mark_is_never_spurious : forall cfg i m eff,
  In (bv_unsigned (in_sysno i)) [214; 222; 226]%Z ->
  alloc_budget_refused_b i m = true ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff Hno Hmark (_ & _ & (eff' & m' & evs' & Hspec & Hnr)).
  destruct Hno as [E | [E | [E | []]]].
  - rewrite (brk_budget_refused_is_refusal _ _ _ _ _ (eq_sym E) Hmark Hspec) in Hnr.
    discriminate Hnr.
  - rewrite (mmap_budget_refused_is_refusal _ _ _ _ _ (eq_sym E) Hmark Hspec) in Hnr.
    discriminate Hnr.
  - rewrite (mprotect_budget_refused_is_refusal _ _ _ _ _ (eq_sym E) Hmark Hspec) in Hnr.
    discriminate Hnr.
Qed.

Lemma marked_step_is_configured : forall cfg segs ms model x8 evs st,
  ms_svc_pending ms = Some x8 ->
  In (bv_unsigned x8) [214; 222; 226]%Z ->
  alloc_budget_refused_b (sys_input segs ms x8) model = true ->
  sstep segs (mkCfg ms model) evs st ->
  sstep_cfg segs cfg (mkCfg ms model) evs st.
Proof.
  intros cfg segs ms model x8 evs st Hsvc Hno Hmark Hss.
  inversion Hss; subst; try congruence; unify_svc x8.
  - eapply sstep_cfg_syscall; try eassumption.
    apply mark_is_never_spurious; [exact Hno | exact Hmark].
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption.
    apply mark_is_never_spurious; [exact Hno | exact Hmark].
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

(** ** The refutations, fired

    [Checks.Omni.ebreak_image] never allocates — its one instruction
    faults — so it satisfies the premise at every budget, and it errors
    at every budget and under every configuration.  A stated refutation
    nobody fires is indistinguishable from one whose hypotheses cannot
    be met, so both refutation lemmas are fired on it here, against a
    target with a valid entry. *)
Example demo_entry_valid_ebreak : forall inp,
  valid_input inp -> valid_entry ebreak_image demo_entry inp.
Proof.
  intros inp Hvalid.
  rewrite (valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvalid)).
  destruct Hvalid as (Hargv & Henvp & _).
  pose proof (entry_stack_span_bound _ _ Hargv Henvp).
  cbn [ebreak_image demo_entry].
  unfold valid_sp, valid_brk, valid_mmap_base, entry_stack_fits.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  unfold entry_stack_span_max, sp_window_lo, sp_window_hi in *.
  repeat split; try lia; vm_compute; try reflexivity; try discriminate.
Qed.

Lemma ebreak_source_within_budget : forall lim,
  source_within_budget lim ebreak_image demo_entry demo_proc_input.
Proof.
  intros lim. unfold source_within_budget, run_budget_refused.
  cbn [ebreak_image demo_entry]. rewrite ebreak_config.
  intros (tr & c & Hstar & Hb).
  inversion Hstar as [c0 Heq | c1 evs c2 tr' c3 Hss Hstar']; subst.
  - exact (ebreak_fault_is_not_budget_refused lim Hb).
  - destruct (ebreak_only _ _ _ Hss) as (_ & Habs). discriminate Habs.
Qed.

Lemma ebreak_errors : forall lim,
  bh_errors (run ebreak_image lim demo_entry demo_proc_input).
Proof.
  intros lim. cbn [run ebreak_image demo_entry bh_errors]. rewrite ebreak_config.
  exists [], (mkCfg ebreak_ms (ebreak_model lim)), []. split; [apply star_refl |].
  apply sstep_instr_fault; [reflexivity | reflexivity |].
  no_lazy. rewrite ebreak_faults. reflexivity.
Qed.

Lemma ebreak_errors_cfg : forall cfg lim,
  bh_errors (run_scfg cfg ebreak_image lim demo_entry demo_proc_input).
Proof.
  intros cfg lim. cbn [run_scfg ebreak_image demo_entry bh_errors]. rewrite ebreak_config.
  exists [], (mkCfg ebreak_ms (ebreak_model lim)), []. split; [apply star_cfg_refl |].
  apply sstep_cfg_instr_fault; [reflexivity | reflexivity |].
  no_lazy. rewrite ebreak_faults. reflexivity.
Qed.

Theorem ebreak_refutes_error_free_budgets : forall lim_source lim_target,
  ~ strong_universal_error_free_T_budgets lim_source lim_target ebreak_image exit0_image.
Proof.
  intros ls lt.
  apply (strong_universal_error_free_T_budgets_refuted_by_source_error
           _ _ _ _ demo_entry demo_entry demo_proc_input).
  - apply demo_entry_valid_ebreak. exact demo_input_valid.
  - apply demo_entry_valid_exit0. exact demo_input_valid.
  - exact demo_input_valid.
  - apply ebreak_source_within_budget.
  - apply ebreak_errors.
Qed.

Theorem ebreak_refutes_error_free_scfg_budgets : forall cfg lim_source lim_target,
  ~ strong_universal_error_free_T_scfg_budgets cfg lim_source lim_target
      ebreak_image exit0_image.
Proof.
  intros cfg ls lt.
  apply (strong_universal_error_free_T_scfg_budgets_refuted_by_source_error
           _ _ _ _ _ demo_entry demo_entry demo_proc_input).
  - apply demo_entry_valid_ebreak. exact demo_input_valid.
  - apply demo_entry_valid_exit0. exact demo_input_valid.
  - exact demo_input_valid.
  - apply source_within_budget_scfg_of_source_within_budget.
    apply ebreak_source_within_budget.
  - apply ebreak_errors_cfg.
Qed.

(* =========================================================================
   PART 6 — the abort-declared configured budget cell
   ========================================================================= *)

(** ** The exit-0 pair under the abort declaration and a configuration

    [Checks.AbortWitness.abrt_input] is the demo input with the abort
    declaration on, valid for [Run.valid_input_abort]
    ([Checks.AbortWitness.abrt_input_valid]).  The exit-0 image is
    entered at [demo_entry] as before — the entry's validity reads only
    the argv and envp clauses, which both stances carry in the same
    positions — and its trace set under any configuration is the
    prefixes of its one exit ([exit0_obs_cfg]), so it is never killed
    and the abort-declared configured statement holds of the pair at
    every configuration and budget pair. *)
Example demo_entry_valid_exit0_abort : forall inp,
  valid_input_abort inp -> valid_entry exit0_image demo_entry inp.
Proof.
  intros inp Hvalid.
  rewrite (valid_entry_sv48 _ _ _ (valid_input_abort_va_size _ Hvalid)).
  destruct Hvalid as (Hargv & Henvp & _).
  pose proof (entry_stack_span_bound _ _ Hargv Henvp).
  cbn [exit0_image demo_entry].
  unfold valid_sp, valid_brk, valid_mmap_base, entry_stack_fits.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  unfold entry_stack_span_max, sp_window_lo, sp_window_hi in *.
  repeat split; try lia; vm_compute; try reflexivity; try discriminate.
Qed.

Lemma exit0_never_dies_by_signal_cfg : forall cfg lim en inp,
  ~ dies_by_signal (run_scfg cfg exit0_image lim en inp).
Proof.
  intros cfg lim [sp brk0 mbase rnd] inp (tr & sig & fs & Htr & Hin).
  cbn [run_scfg exit0_image bh_traces] in Htr. apply exit0_obs_cfg in Htr.
  destruct tr as [| e tr']; [exact Hin |].
  destruct Htr as [-> Htr']. destruct tr' as [| e' tr'']; [| destruct Htr'].
  destruct Hin as [Hin | []]. discriminate Hin.
Qed.

Theorem exit0_strong_universal_error_free_budgets_scfg_abort : forall cfg lim_source lim_target,
  strong_universal_error_free_T_scfg_budgets_abort cfg lim_source lim_target
    exit0_image exit0_image.
Proof.
  intros cfg ls lt [sps brks mbs rnds] [spt brkt mbt rndt] inp _ _ _ _.
  unfold strong_equiv_error_free_budgets_scfg_abort, error_free_unkilled.
  split; [| split].
  - split; [| apply exit0_never_dies_by_signal_cfg].
    apply error_free_scfg_of_error_free.
    apply error_free_iff. cbn [omni_corun exit0_image img_segments].
    apply exit0_never_errors.
  - split; [| apply exit0_never_dies_by_signal_cfg].
    apply error_free_scfg_of_error_free.
    apply error_free_iff. cbn [omni_corun exit0_image img_segments].
    apply exit0_never_errors.
  - intros tr. cbn [run_scfg exit0_image bh_traces].
    rewrite !exit0_obs_cfg. reflexivity.
Qed.

Module Exit0ScfgBudgetsAbortChecked
  <: SPEC_ERROR_FREE_SCFG_BUDGETS_ABORT ForcedOnlyCfg ShippedBudgets Exit0Image Exit0Image.
  Definition strong_universal_error_free :=
    exit0_strong_universal_error_free_budgets_scfg_abort ForcedOnlyCfg.cfg
      ShippedBudgets.lim_source ShippedBudgets.lim_target.
End Exit0ScfgBudgetsAbortChecked.

Module Exit0ScfgBudgetsAbortBaselineChecked
  <: SPEC_SCFG_BUDGETS_ABORT ForcedOnlyCfg ShippedBudgets Exit0Image Exit0Image.
  Definition strong_universal :=
    strong_universal_error_free_T_scfg_budgets_abort_implies _ _ _ _ _
      Exit0ScfgBudgetsAbortChecked.strong_universal_error_free.
End Exit0ScfgBudgetsAbortBaselineChecked.

(** ** The refutation, fired under the abort declaration

    [Checks.Omni.ebreak_image] serves under the declaration as it does
    without it: its one instruction faults before any syscall, so the
    declaration — which only changes what [tkill] does — never comes
    into play.  The machine state at [abrt_input] is [Checks.Omni.ebreak_ms]
    (the two inputs differ only in the declaration, which the entry
    does not read); only the model carries the flag. *)
Definition ebreak_model_abort (lim : Z) : Model :=
  init_model (segments_reserved ebreak_segments) (Z_to_bv 64 0x1000)
    (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000) lim abrt_input.

Lemma ebreak_config_abort : forall lim,
  init_config ebreak_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim abrt_input
  = mkCfg ebreak_ms (ebreak_model_abort lim).
Proof. reflexivity. Qed.

Lemma ebreak_only_abort : forall lim evs st,
  sstep ebreak_segments (mkCfg ebreak_ms (ebreak_model_abort lim)) evs st ->
  evs = [] /\ st = SError.
Proof.
  intros lim. apply sstep_fault_only; [reflexivity | reflexivity | exact ebreak_faults].
Qed.

(** The fault is not a budget refusal whatever the model beside it:
    [ebreak_fault_is_not_budget_refused] generalised. *)
Lemma ebreak_fault_is_not_budget_refused_any : forall model,
  ~ budget_refused_at ebreak_segments (mkCfg ebreak_ms model).
Proof.
  intros model (_ & [(_ & r & E & _) | (x8 & Hx8 & _)]); cbn [cfg_ms cfg_model] in *.
  - pose proof (drop_step_accesses ebreak_segments ebreak_ms) as Hd.
    rewrite E, ebreak_faults in Hd. discriminate Hd.
  - assert (Hnone : ms_svc_pending ebreak_ms = None) by reflexivity.
    congruence.
Qed.

Example demo_entry_valid_ebreak_abort : forall inp,
  valid_input_abort inp -> valid_entry ebreak_image demo_entry inp.
Proof.
  intros inp Hvalid.
  rewrite (valid_entry_sv48 _ _ _ (valid_input_abort_va_size _ Hvalid)).
  destruct Hvalid as (Hargv & Henvp & _).
  pose proof (entry_stack_span_bound _ _ Hargv Henvp).
  cbn [ebreak_image demo_entry].
  unfold valid_sp, valid_brk, valid_mmap_base, entry_stack_fits.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  unfold entry_stack_span_max, sp_window_lo, sp_window_hi in *.
  repeat split; try lia; vm_compute; try reflexivity; try discriminate.
Qed.

Lemma ebreak_source_within_budget_abort : forall lim,
  source_within_budget lim ebreak_image demo_entry abrt_input.
Proof.
  intros lim. unfold source_within_budget, run_budget_refused.
  cbn [ebreak_image demo_entry]. rewrite ebreak_config_abort.
  intros (tr & c & Hstar & Hb).
  inversion Hstar as [c0 Heq | c1 evs c2 tr' c3 Hss Hstar']; subst.
  - exact (ebreak_fault_is_not_budget_refused_any _ Hb).
  - destruct (ebreak_only_abort _ _ _ Hss) as (_ & Habs). discriminate Habs.
Qed.

Lemma ebreak_errors_cfg_abort : forall cfg lim,
  bh_errors (run_scfg cfg ebreak_image lim demo_entry abrt_input).
Proof.
  intros cfg lim. cbn [run_scfg ebreak_image demo_entry bh_errors].
  rewrite ebreak_config_abort.
  exists [], (mkCfg ebreak_ms (ebreak_model_abort lim)), []. split; [apply star_cfg_refl |].
  apply sstep_cfg_instr_fault; [reflexivity | reflexivity |].
  no_lazy. rewrite ebreak_faults. reflexivity.
Qed.

Theorem ebreak_refutes_error_free_scfg_budgets_abort : forall cfg lim_source lim_target,
  ~ strong_universal_error_free_T_scfg_budgets_abort cfg lim_source lim_target
      ebreak_image exit0_image.
Proof.
  intros cfg ls lt.
  apply (strong_universal_error_free_T_scfg_budgets_abort_refuted_by_source_error
           _ _ _ _ _ demo_entry demo_entry abrt_input).
  - apply demo_entry_valid_ebreak_abort. exact abrt_input_valid.
  - apply demo_entry_valid_exit0_abort. exact abrt_input_valid.
  - exact abrt_input_valid.
  - apply source_within_budget_scfg_of_source_within_budget.
    apply ebreak_source_within_budget_abort.
  - apply ebreak_errors_cfg_abort.
Qed.
