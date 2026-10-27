(** * LinuxProcessSem.Checks.OversizeReachable — the finer budget premise, on runs

    Not part of the trusted specification.  As [Checks.BudgetPremise]
    does for the released premise, this shows both directions on runs:

    - the finer premise holds of the [BudgetPremise.mm_image] run, which
      the released premise excludes, and the finer statement is refuted
      on it ([mm_within_budget_only], [mm_errors],
      [mm_refutes_budgets_only]);
    - it excludes a run whose second one-page mmap at a one-page budget
      is refused for budget ([cm_not_within_budget_only]). *)
From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs Examples SpuriousCfg Omni BudgetPremise.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* =========================================================================
   The oversize refusal: in scope of the finer premise
   ========================================================================= *)

(** The request pending at [BudgetPremise.mm_s 6]. *)
Definition mm_i : SyscallInput := sys_input mm_segments (mm_s 6) (Z_to_bv 64 222).

Lemma mm_i_budget_refused : alloc_budget_refused_b mm_i mm_model = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mm_i_classifies_oversize : alloc_refuse_reason mm_i mm_model = Some RefuseOversize.
Proof. vm_compute. reflexivity. Qed.

Definition mm_eff : SyscallEffect := mkEffect (errno_ret ENOMEM) [] [].

Definition mm_ms7 : machine_state := advance_past_svc (apply_effect (mm_s 6) mm_eff).

Lemma mm_arg0 : in_arg mm_i 0 = Z_to_bv 64 0.
Proof. vm_compute. first [reflexivity | apply bv_eq; reflexivity]. Qed.
Lemma mm_arg1 : in_arg mm_i 1 = Z_to_bv 64 8192.
Proof. vm_compute. first [reflexivity | apply bv_eq; reflexivity]. Qed.
Lemma mm_arg2 : in_arg mm_i 2 = Z_to_bv 64 3.
Proof. vm_compute. first [reflexivity | apply bv_eq; reflexivity]. Qed.
Lemma mm_arg3 : in_arg mm_i 3 = Z_to_bv 64 34.
Proof. vm_compute. first [reflexivity | apply bv_eq; reflexivity]. Qed.
Lemma mm_arg4 : in_arg mm_i 4 = Z_to_bv 64 (-1).
Proof. vm_compute. first [reflexivity | apply bv_eq; reflexivity]. Qed.
Lemma mm_arg5 : in_arg mm_i 5 = Z_to_bv 64 0.
Proof. vm_compute. first [reflexivity | apply bv_eq; reflexivity]. Qed.

Lemma mm_sysno : bv_unsigned (in_sysno mm_i) = 222%Z.
Proof. reflexivity. Qed.

(** Every outcome the kernel admits at the ecall is the -ENOMEM refusal,
    with the model unchanged. *)
Lemma mm_ecall_only : forall o,
  syscall_spec mm_i mm_model o -> o = Ok mm_eff mm_model [].
Proof.
  intros o H.
  apply (proj1 (mmap_dispatch mm_i mm_model o mm_sysno)) in H.
  rewrite mm_arg0, mm_arg1, mm_arg2, mm_arg3, mm_arg4, mm_arg5 in H.
  unfold mmap_spec in H.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 34)) with true in H by (vm_compute; reflexivity).
  replace (w_is0 (Z_to_bv 64 8192)) with false in H by (vm_compute; reflexivity).
  replace (mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true in H
    by (vm_compute; reflexivity).
  cbv beta iota zeta delta [negb] in H.
  unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, get_model, modify in H.
  destruct o as [eff m' evs |]; cbv beta iota zeta in H; sys_destruct;
    first
      [ discriminate
      | match goal with
        | [ Hin : In ?e mmap_errnos |- _ ] => destruct Hin as [<- | []]; reflexivity
        end
      | exfalso;
        match goal with
        | [ Hb : mmap_noreserve_backed_ok _ _ _ = true |- _ ] =>
            vm_compute in Hb; discriminate Hb
        end ].
Qed.

Lemma mm_ecall_admits : syscall_spec mm_i mm_model (Ok mm_eff mm_model []).
Proof.
  apply (proj2 (mmap_dispatch mm_i mm_model _ mm_sysno)).
  rewrite mm_arg0, mm_arg1, mm_arg2, mm_arg3, mm_arg4, mm_arg5.
  unfold mmap_spec.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 34)) with true by (vm_compute; reflexivity).
  replace (w_is0 (Z_to_bv 64 8192)) with false by (vm_compute; reflexivity).
  replace (mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true
    by (vm_compute; reflexivity).
  cbv beta iota zeta delta [negb].
  left. unfold bind, errno_from, choose, err_ret, ret_only, pure.
  exists ENOMEM, mm_model, [], [].
  split; [exists ENOMEM; split; [left; reflexivity | reflexivity] |].
  split; reflexivity.
Qed.

Lemma mm_ms7_svc : ms_svc_pending mm_ms7 = None.
Proof. reflexivity. Qed.

(** After the refusal the program runs off the end of its 24-byte
    segment: the next fetch faults. *)
Lemma mm_ms7_faults : RiscvSemantics.step mm_segments mm_ms7 = MachineFault.
Proof. vm_compute. reflexivity. Qed.

Lemma mm_ms7_accesses_fault :
  forall report, RiscvSemantics.step_accesses mm_segments mm_ms7 <> MachineOk report.
Proof. intros report. vm_compute. discriminate. Qed.

(** "Never budget-only refused from here", closed under [star]. *)
Definition mm_never_bor (c : config) : Prop :=
  forall tr c', star mm_segments c tr c' -> ~ budget_only_refused_at mm_segments c'.

Lemma mm_never_bor_intro : forall c,
  ~ budget_only_refused_at mm_segments c ->
  (forall evs c2, sstep mm_segments c evs (SNext c2) -> mm_never_bor c2) ->
  mm_never_bor c.
Proof.
  intros c Hn Hs tr c' Hstar.
  inversion Hstar as [c0 Heq | c1 evs c2 tr' c3 Hss Hstar']; subst.
  - exact Hn.
  - exact (Hs _ _ Hss _ _ Hstar').
Qed.

Lemma mm_never_bor_c7 : mm_never_bor (mkCfg mm_ms7 mm_model).
Proof.
  apply mm_never_bor_intro.
  - intros (_ & [(_ & report & Hacc & _) | (x8 & Hx8 & _)]); cbn [cfg_ms cfg_model] in *.
    + exact (mm_ms7_accesses_fault report Hacc).
    + rewrite mm_ms7_svc in Hx8. discriminate Hx8.
  - intros evs c2 Hss.
    destruct (sstep_fault_only mm_segments mm_ms7 mm_model eq_refl mm_ms7_svc
                mm_ms7_faults _ _ Hss) as [_ Habs].
    discriminate Habs.
Qed.

Lemma mm_never_bor_c6 : mm_never_bor (mkCfg (mm_s 6) mm_model).
Proof.
  apply mm_never_bor_intro.
  - intros (_ & [(Hnone & _) | (x8 & Hx8 & [Hb | (eff & m' & evs & Hspec & _ & Hmat)])]);
      cbn [cfg_ms cfg_model] in *.
    + rewrite mm_svc6 in Hnone. discriminate Hnone.
    + rewrite mm_svc6 in Hx8. injection Hx8 as <-.
      change (sys_input mm_segments (mm_s 6) (Z_to_bv 64 222)) with mm_i in Hb.
      rewrite mm_i_classifies_oversize in Hb. discriminate Hb.
    + rewrite mm_svc6 in Hx8. injection Hx8 as <-.
      apply mm_ecall_only in Hspec. injection Hspec as -> -> ->.
      rewrite (materialize_model_accesses_no_lazy mm_model _ eq_refl) in Hmat.
      discriminate Hmat.
  - intros evs c2 Hss.
    pose proof mm_svc6 as H6.
    inversion Hss; subst; try congruence;
      match goal with
      | [ Hp : ms_svc_pending (mm_s 6) = Some ?y |- _ ] =>
          rewrite H6 in Hp; injection Hp as <-
      end;
      match goal with
      | [ Hsp : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
          apply mm_ecall_only in Hsp; injection Hsp as -> -> ->
      end;
      try (match goal with
           | [ H : m_halted mm_model = Some _ |- _ ] => vm_compute in H; discriminate H
           | [ H : m_killed mm_model = Some _ |- _ ] => vm_compute in H; discriminate H
           end).
    match goal with
    | [ H : materialize_model_accesses mm_model _ = Some _ |- _ ] =>
        rewrite (materialize_model_accesses_no_lazy mm_model _ eq_refl) in H;
        injection H as <-
    end.
    exact mm_never_bor_c7.
Qed.

Lemma mm_never_bor_k : forall k, (k <= 6)%nat -> mm_never_bor (mkCfg (mm_s k) mm_model).
Proof.
  intros k Hk. remember (6 - k)%nat as d eqn:Hd. revert k Hk Hd.
  induction d as [|d IH]; intros k Hk Hd.
  - assert (k = 6)%nat by lia. subst k. exact mm_never_bor_c6.
  - assert (Hlt : (k < 6)%nat) by lia.
    assert (Hsvc : ms_svc_pending (mm_s k) = None).
    { do 6 (destruct k as [| k]; [vm_compute; reflexivity |]). lia. }
    assert (Hstep : RiscvSemantics.step mm_segments (mm_s k) = MachineOk (mm_s (S k))).
    { unfold mm_s. apply mm_step. exact Hlt. }
    apply mm_never_bor_intro.
    + intro Hb.
      apply (budget_refused_at_no_lazy_instr mm_segments (mm_s k) mm_model eq_refl Hsvc).
      apply budget_only_refused_at_implies. exact Hb.
    + intros evs c2 Hss.
      destruct (sstep_instr_only mm_segments (mm_s k) mm_model (mm_s (S k)) eq_refl Hsvc
                  Hstep _ _ Hss) as [_ Hc2].
      injection Hc2 as ->. apply (IH (S k)); lia.
Qed.

(** The finer premise HOLDS of the mm run ... *)
Theorem mm_within_budget_only :
  source_within_budget_only mm_budget mm_image demo_entry demo_proc_input.
Proof.
  change (~ reaches_budget_only_refused mm_segments
            (init_config mm_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
               (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw mm_budget
               demo_proc_input)).
  rewrite mm_config.
  intros (tr & c & Hstar & Hb).
  exact (mm_never_bor_k 0 ltac:(lia) tr c Hstar Hb).
Qed.

(** ... which the released premise does not
    ([BudgetPremise.mm_not_within_budget]). *)

(** The mm run errors: the refusal, then a fetch fault. *)
Lemma mm_errors : bh_errors (run mm_image mm_budget demo_entry demo_proc_input).
Proof.
  cbn [run mm_image demo_entry bh_errors]. rewrite mm_config.
  exists ([] ++ []), (mkCfg mm_ms7 mm_model), []. split.
  - eapply star_trans; [exact mm_star |].
    apply star_one.
    apply (sstep_syscall mm_segments (mm_s 6) mm_model (Z_to_bv 64 222) mm_eff
             mm_model mm_model []).
    + vm_compute. reflexivity.
    + exact mm_svc6.
    + exact mm_ecall_admits.
    + vm_compute. reflexivity.
    + apply materialize_model_accesses_no_lazy. vm_compute. reflexivity.
  - apply sstep_instr_fault; [vm_compute; reflexivity | exact mm_ms7_svc |].
    no_lazy. rewrite mm_ms7_faults. reflexivity.
Qed.

Lemma demo_entry_valid_mm : forall inp,
  valid_input inp -> valid_entry mm_image demo_entry inp.
Proof.
  intros inp Hvalid.
  rewrite (valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvalid)).
  destruct Hvalid as (Hargv & Henvp & _).
  pose proof (entry_stack_span_bound _ _ Hargv Henvp).
  cbn [mm_image demo_entry].
  unfold valid_sp, valid_brk, valid_mmap_base, entry_stack_fits.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  unfold entry_stack_span_max, sp_window_lo, sp_window_hi in *.
  repeat split; try lia; vm_compute; try reflexivity; try discriminate.
Qed.

(** [strong_universal_error_free_T_budgets_only_refuted_by_source_error],
    fired: the finer statement is false of the mm run paired with the
    exit-0 image, at its one-page budget and every target budget.  The
    released statement at the same budgets says nothing about this
    input. *)
Theorem mm_refutes_budgets_only : forall lim_target,
  ~ strong_universal_error_free_T_budgets_only mm_budget lim_target mm_image exit0_image.
Proof.
  intros lt.
  apply (strong_universal_error_free_T_budgets_only_refuted_by_source_error
           mm_budget lt mm_image exit0_image demo_entry demo_entry demo_proc_input).
  - apply demo_entry_valid_mm. exact demo_input_valid.
  - apply demo_entry_valid_exit0. exact demo_input_valid.
  - exact demo_input_valid.
  - exact mm_within_budget_only.
  - exact mm_errors.
Qed.

(** The exit-0 image satisfies the finer premise at every budget. *)
Lemma exit0_source_within_budget_only : forall lim en inp,
  source_within_budget_only lim exit0_image en inp.
Proof.
  intros lim en inp Hc.
  exact (exit0_never_budget_refused lim en inp (run_budget_only_refused_implies _ _ _ _ Hc)).
Qed.

(* =========================================================================
   A cumulative refusal: excluded by the finer premise
   ========================================================================= *)

(** Seven instructions at 0x100: two
    [mmap(addr, 4096, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0)]
    calls.  The first passes [addr = 0].  The second passes the address
    the first returned, which stays in [a0]; without MAP_FIXED it is only
    a hint, and the hint-placed branch does not read it.  At a one-page
    budget the first may be granted, and the second is then refused with
    a charge equal to the budget. *)
Definition cm_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 28;
  seg_perms := "r-x"%string;
  seg_bytes := ["9308e00db715000013063000930620021307f0ff7300000073000000"%pstring]
|}.
Definition cm_segments : list Segment := [cm_segment].
Definition cm_image : Image := mkImage cm_segments 0x100 demo_phdrs.

Definition cm_budget : Z := page_size.

Definition cm_ms0 : machine_state :=
  init_machine_state cm_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    demo_draw
    (in_argv demo_proc_input) (in_envp demo_proc_input) (in_uid demo_proc_input)
    (in_hwcap demo_proc_input).
Definition cm_msk (k : nat) : machine_state :=
  match run_steps k cm_segments cm_ms0 with
  | Some ms => ms
  | None => cm_ms0
  end.
Definition cm_s (k : nat) : machine_state := with_mem (cm_msk k) (ms_mem cm_ms0).

Definition cm_model : Model :=
  init_model (segments_reserved cm_segments) (Z_to_bv 64 0x1000)
    (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000) cm_budget demo_proc_input.
Definition cm_c : config := mkCfg (cm_s 0) cm_model.

Lemma cm_config :
  init_config cm_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw cm_budget demo_proc_input
  = cm_c.
Proof. unfold init_config, cm_c. f_equal; try exact (with_mem_eta cm_ms0). Qed.

Lemma cm_step : forall k, (k < 6)%nat -> forall mem,
  RiscvSemantics.step cm_segments (with_mem (cm_msk k) mem)
  = MachineOk (with_mem (cm_msk (S k)) mem).
Proof.
  intros k Hk mem.
  do 6 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
Qed.

Lemma cm_instr_sstep : forall k, (k < 6)%nat ->
  sstep cm_segments (mkCfg (cm_s k) cm_model) []
    (SNext (mkCfg (cm_s (S k)) cm_model)).
Proof.
  intros k Hk. unfold cm_s.
  apply sstep_instr; [reflexivity | |].
  - do 6 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
  - no_lazy. rewrite (cm_step k Hk). reflexivity.
Qed.

Lemma cm_svc6 : ms_svc_pending (cm_s 6) = Some (Z_to_bv 64 222).
Proof. vm_compute. first [reflexivity | f_equal; apply bv_eq; reflexivity]. Qed.

Lemma cm_star6 : star cm_segments cm_c [] (mkCfg (cm_s 6) cm_model).
Proof.
  change (@nil event) with
    ((@nil event) ++ ((@nil event) ++ ((@nil event) ++ ((@nil event) ++
     ((@nil event) ++ ((@nil event) ++ (@nil event))))))).
  unfold cm_c.
  eapply star_step; [exact (cm_instr_sstep 0 ltac:(lia)) |].
  eapply star_step; [exact (cm_instr_sstep 1 ltac:(lia)) |].
  eapply star_step; [exact (cm_instr_sstep 2 ltac:(lia)) |].
  eapply star_step; [exact (cm_instr_sstep 3 ltac:(lia)) |].
  eapply star_step; [exact (cm_instr_sstep 4 ltac:(lia)) |].
  eapply star_step; [exact (cm_instr_sstep 5 ltac:(lia)) |].
  apply star_refl.
Qed.

(** The first request, before any grant: within budget, so not refused. *)
Definition cm_i1 : SyscallInput := sys_input cm_segments (cm_s 6) (Z_to_bv 64 222).

Lemma cm_ecall1_not_refused : alloc_refuse_reason cm_i1 cm_model = None.
Proof. vm_compute. reflexivity. Qed.

(** THE ADDRESS THE MODEL CHOOSES.  The hint-placed branch admits any
    positive, page-aligned, free address whose mapping ends at or below
    [State.alloc_top], when its budget gate passes; this effect names
    one, and [cm_sc1] is the acceptor's statement that it is admissible. *)
Definition cm_addr : word := Z_to_bv 64 0x10000000.

Definition cm_eff1 : SyscallEffect := mkEffect cm_addr [] [(cm_addr, Z_to_bv 64 4096)].

Definition cm_model1 : Model :=
  match check_syscall cm_i1 cm_eff1 cm_model with
  | CheckOk m _ => m
  | _ => cm_model
  end.

Lemma cm_sc1 : check_syscall cm_i1 cm_eff1 cm_model = CheckOk cm_model1 [].
Proof. vm_compute. reflexivity. Qed.

Lemma cm_sc1_spec : syscall_spec cm_i1 cm_model (Ok cm_eff1 cm_model1 []).
Proof. exact (proj1 (check_syscall_ok_iff cm_i1 cm_eff1 cm_model cm_model1 []) cm_sc1). Qed.

(** The state the first call leaves: a0 holds the address, the page is
    zeroed, and the pc is at the second [ecall]. *)
Definition cm_t0 : machine_state := advance_past_svc (apply_effect (cm_s 6) cm_eff1).
Definition cm_tk (k : nat) : machine_state :=
  match run_steps k cm_segments cm_t0 with
  | Some ms => ms
  | None => cm_t0
  end.
Definition cm_t (k : nat) : machine_state := with_mem (cm_tk k) (ms_mem cm_t0).

Lemma cm_t0_eq : cm_t 0 = cm_t0.
Proof. unfold cm_t, cm_tk. cbn [run_steps]. symmetry. apply with_mem_eta. Qed.

Lemma cm_syscall1_sstep :
  sstep cm_segments (mkCfg (cm_s 6) cm_model) []
    (SNext (mkCfg (cm_t 0) cm_model1)).
Proof.
  rewrite cm_t0_eq. unfold cm_t0.
  apply (sstep_syscall cm_segments (cm_s 6) cm_model (Z_to_bv 64 222) cm_eff1
           cm_model1 cm_model1 []).
  - reflexivity.
  - exact cm_svc6.
  - exact cm_sc1_spec.
  - vm_compute. reflexivity.
  - apply materialize_model_accesses_no_lazy. vm_compute. reflexivity.
Qed.

Lemma cm_step2 : forall mem,
  RiscvSemantics.step cm_segments (with_mem (cm_tk 0) mem)
  = MachineOk (with_mem (cm_tk 1) mem).
Proof. intros mem. vm_compute. reflexivity. Qed.

Lemma cm_instr2_sstep :
  sstep cm_segments (mkCfg (cm_t 0) cm_model1) [] (SNext (mkCfg (cm_t 1) cm_model1)).
Proof.
  unfold cm_t.
  apply sstep_instr; [vm_compute; reflexivity | vm_compute; reflexivity |].
  no_lazy. rewrite cm_step2. reflexivity.
Qed.

Lemma cm_svc_t1 : ms_svc_pending (cm_t 1) = Some (Z_to_bv 64 222).
Proof. vm_compute. first [reflexivity | f_equal; apply bv_eq; reflexivity]. Qed.

(** The second request: budget-refused, with a charge of one page, equal
    to the budget and not above it, so the classifier gives
    [RefuseBudget]. *)
Definition cm_i2 : SyscallInput := sys_input cm_segments (cm_t 1) (Z_to_bv 64 222).

Lemma cm_ecall2_charge :
  alloc_req_charge_bytes cm_i2 cm_model1 = cm_budget
  /\ vm_limit (m_vmmaps cm_model1) = cm_budget.
Proof. vm_compute. split; reflexivity. Qed.

Lemma cm_ecall2_classifies_budget :
  alloc_refuse_reason cm_i2 cm_model1 = Some RefuseBudget.
Proof. vm_compute. reflexivity. Qed.

Lemma cm_ecall2_is_budget_only_refused :
  budget_only_refused_at cm_segments (mkCfg (cm_t 1) cm_model1).
Proof.
  split; [vm_compute; reflexivity |]. right.
  exists (Z_to_bv 64 222). split; [exact cm_svc_t1 |]. left.
  exact cm_ecall2_classifies_budget.
Qed.

Theorem cm_run_budget_only_refused :
  run_budget_only_refused cm_image cm_budget demo_entry demo_proc_input.
Proof.
  change (reaches_budget_only_refused cm_segments
            (init_config cm_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
               (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw cm_budget
               demo_proc_input)).
  rewrite cm_config.
  eexists. eexists. split; [| exact cm_ecall2_is_budget_only_refused].
  eapply star_trans; [exact cm_star6 |].
  eapply star_step; [exact cm_syscall1_sstep |].
  eapply star_step; [exact cm_instr2_sstep |].
  apply star_refl.
Qed.

(** ... so the finer premise excludes this run, and with it the released
    premise ([Equivalence.source_within_budget_only_of_source_within_budget]). *)
Theorem cm_not_within_budget_only :
  ~ source_within_budget_only cm_budget cm_image demo_entry demo_proc_input.
Proof. intros H. exact (H cm_run_budget_only_refused). Qed.

Theorem cm_not_within_budget :
  ~ source_within_budget cm_budget cm_image demo_entry demo_proc_input.
Proof.
  intros H.
  exact (cm_not_within_budget_only
           (source_within_budget_only_of_source_within_budget _ _ _ _ H)).
Qed.
