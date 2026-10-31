(** * LinuxProcessSem.Checks.SpuriousCfg — the forced-only filter, on cases chosen by hand

    Not part of the trusted specification: this file is QA on
    [Run.SpuriousCfg], [Run.spurious_refusal_cfg] and [Run.sstep_cfg],
    written to be READ, in the manner of [Checks.Examples] and under the
    four admission reasons its header lists.  Every case here is one a
    single real run cannot show, and for one reason above all: a fold
    of the checker sees what the kernel DID, and the filter is
    a statement about what the kernel COULD HAVE DONE instead — whether
    a refusal was avoidable — which is not an observation of any one
    run (reason 4, and reason 3 where a fixture's budget or ledger is
    named).

    ** What is pinned, family by family

    - fs, never forced: [getcwd]'s -ENOMEM is spurious under forced-only
      and kept under may-fail; its -ERANGE, the answer the state
      determines, is kept under both.  At the STEP level this is the
      subset lemma's negative twin — [Run.sstep] admits the -ENOMEM
      step and [Run.sstep_cfg Run.forced_only_cfg] refuses it — with
      the -ERANGE step admitted on both sides as the positive twin.
    - cred, keyed on state: [setsid]'s -EPERM is spurious before a
      success and FORCED after one, because [Kernel.Sys.setsid_spec]
      answers it deterministically once [State.m_setsid_succeeded] is
      set.
    - alloc, keyed on the budget: an anonymous [mmap] within budget has
      its -ENOMEM removed; one beyond the budget keeps it, because the
      grant's [choose] has no witness there.  And an -ENOMEM the ARGUMENT
      gate determines — the overflowing MAP_FIXED length of
      [Checks.Cases.Mm.Mmap.mmap_fixed_overflowing_len_is_enomem] — is
      kept although it is in [Mmap.mmap_errnos], which is the exactness
      argument of [Run.v]'s spurious-failure header made concrete: the
      filter never removes an answer the state determines, whatever the
      list says.
    - the table itself: sorted, and every number in it dispatches.
    - four refusals no state forces, at every input and model:
      [munmap]'s -ENOMEM on a whole or a partial unmap (alloc),
      [faccessat2]'s -ENOMEM
      and -EACCES, [getdents64]'s -ENOENT and [write]'s -ENOMEM on a
      pipe whose queue is empty (fs).  Wherever the spec
      admits one of them it admits a non-refusal beside it, so a
      configuration that reads the family as forced-only removes every
      such answer and one that reads it as may-fail keeps it: forced-only
      removes all four, [alloc_only_cfg false] only [munmap]'s.
    - run level: the exit-0 image must-exits under forced-only exactly
      as it does under may-fail, and the undecodable image refutes the
      predicate under forced-only as it does under may-fail — the two
      witnesses [MustExit]'s header points at, at the other reading. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Examples.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit Classifier.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* =========================================================================
   PART 1 — the table
   ========================================================================= *)

Fixpoint strictly_ascending (l : list Z) : bool :=
  match l with
  | a :: ((b :: _) as r) => Z.ltb a b && strictly_ascending r
  | _ => true
  end.

(** Sorted by number, like [Sys.SyscallTable.spec_table], and so with no
    number twice — the property [Run.lookup_injected]'s first-match
    lookup needs to be unambiguous. *)
Example injected_table_sorted :
  strictly_ascending (map ia_no injected_table) = true.
Proof. vm_compute. reflexivity. Qed.

(** Every injecting arm names a syscall the dispatcher answers: a number
    here with no arm in [Sys.SyscallTable.spec_table] would be a filter
    on nothing. *)
Example injected_table_dispatches :
  forallb (fun a => existsb (Z.eqb (ia_no a)) (arm_numbers spec_table))
          injected_table = true.
Proof. vm_compute. reflexivity. Qed.

(** An effect that answers errno [e] and does nothing else. *)
Definition errno_eff (e : Z) : SyscallEffect := mkEffect (errno_ret e) [] [].

(** The model every check below starts from: the demo process with an
    empty file system and end of input. *)
Definition m0 : Model := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

(* =========================================================================
   PART 2 — which families a configuration turns off
   ========================================================================= *)

(** A machine state at a [getcwd] ecall: syscall number 17 pending, every
    register 0 — so [size] is 0, inside the band [DPath.getcwd_spec]
    answers — and no memory at all, which that spec never reads. *)
Definition getcwd_ms : machine_state := {|
  ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
  ms_pc_val := Z_to_bv 64 0x100;
  ms_svc_pending := Some (Z_to_bv 64 17);
  ms_resv := None; ms_fcsr := Z_to_bv 32 0;
  ms_mem := fun _ => None; ms_rom := fun _ => None |}.

Definition getcwd_i : SyscallInput := sys_input [] getcwd_ms (Z_to_bv 64 17).

Example getcwd_off_under_forced_only :
  injected_family_off forced_only_cfg getcwd_i = true.
Proof. vm_compute. reflexivity. Qed.

Example getcwd_on_under_may_fail :
  injected_family_off may_fail_cfg getcwd_i = false.
Proof. vm_compute. reflexivity. Qed.

(** The one-switch form [alloc_only_cfg] touches the allocation family
    and nothing else. *)
Example getcwd_on_under_alloc_only :
  injected_family_off (alloc_only_cfg false) getcwd_i = false.
Proof. vm_compute. reflexivity. Qed.

Example mmap_off_under_alloc_only :
  injected_family_off (alloc_only_cfg false) (mmap_in 4096) = true.
Proof. vm_compute. reflexivity. Qed.

(** A syscall with no injecting arm belongs to no family, whatever the
    configuration: [exit] is never filtered. *)
Example exit_has_no_family : forall cfg,
  injected_family_off cfg
    (mkInput 93 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None)) = false.
Proof. intros cfg. vm_compute. reflexivity. Qed.

(* =========================================================================
   PART 3 — fs: getcwd, never forced
   ========================================================================= *)

Lemma getcwd_dispatch : forall m o,
  syscall_spec getcwd_i m o <-> getcwd_spec (in_arg getcwd_i 1) getcwd_i m o.
Proof.
  intros m o. unfold syscall_spec, dispatch.
  assert (E : bv_unsigned (in_sysno getcwd_i) = 17%Z) by (vm_compute; reflexivity).
  rewrite E. reflexivity.
Qed.

Lemma getcwd_size_in_band : (1 <? bv_unsigned (in_arg getcwd_i 1))%Z = false.
Proof. vm_compute. reflexivity. Qed.

(** Every answer [getcwd] admits here: -ERANGE, or one of the injected
    three; the model is untouched and nothing is emitted. *)
Lemma getcwd_admits : forall m e,
  In e (ERANGE :: getcwd_errnos) ->
  syscall_spec getcwd_i m (Ok (errno_eff e) m []).
Proof.
  intros m e Hin. apply getcwd_dispatch. unfold getcwd_spec.
  rewrite getcwd_size_in_band.
  destruct Hin as [<- | Hin].
  - apply alt_r. reflexivity.
  - apply alt_l. unfold errno_from, bind, choose.
    exists e, m, [], [].
    split; [exists e; split; [exact Hin | reflexivity] |].
    split; reflexivity.
Qed.

Lemma getcwd_only : forall m eff m' evs,
  syscall_spec getcwd_i m (Ok eff m' evs) ->
  m' = m /\ evs = [] /\ exists e, In e (ERANGE :: getcwd_errnos) /\ eff = errno_eff e.
Proof.
  intros m eff m' evs H. apply (proj1 (getcwd_dispatch m _)) in H. unfold getcwd_spec in H.
  rewrite getcwd_size_in_band in H.
  unfold alt, errno_from, bind, choose, err_ret, ret_only, pure in H.
  sys_destruct;
    (split; [reflexivity | split; [reflexivity |]]);
    first [ match goal with
            | [ Hin : In ?e getcwd_errnos |- _ ] =>
                exists e; split; [right; exact Hin | reflexivity]
            end
          | exists ERANGE; split; [left; reflexivity | reflexivity] ].
Qed.

(** The -ENOMEM is spurious under forced-only: -ERANGE was available. *)
Example getcwd_enomem_spurious_under_forced_only :
  spurious_refusal_cfg forced_only_cfg getcwd_i m0 (errno_eff ENOMEM).
Proof.
  split; [exact getcwd_off_under_forced_only |].
  split; [vm_compute; reflexivity |].
  exists (errno_eff ERANGE), m0, []. split.
  - apply getcwd_admits. left. reflexivity.
  - vm_compute. reflexivity.
Qed.

(** ... and kept under may-fail, and under a configuration that turns
    only the allocation family off. *)
Example getcwd_enomem_kept_under_may_fail :
  ~ spurious_refusal_cfg may_fail_cfg getcwd_i m0 (errno_eff ENOMEM).
Proof. apply spurious_refusal_may_fail. Qed.

Example getcwd_enomem_kept_under_alloc_only :
  ~ spurious_refusal_cfg (alloc_only_cfg false) getcwd_i m0 (errno_eff ENOMEM).
Proof. apply spurious_refusal_family_on. exact getcwd_on_under_alloc_only. Qed.

(** The answer the state determines is never spurious. *)
Example getcwd_erange_kept_under_forced_only :
  ~ spurious_refusal_cfg forced_only_cfg getcwd_i m0 (errno_eff ERANGE).
Proof. apply spurious_refusal_not_refusal. vm_compute. reflexivity. Qed.

(** The filter's question is answered here, in the affirmative. *)
Example getcwd_decided :
  refusal_decided forced_only_cfg getcwd_i m0.
Proof.
  intros _. left. exists (errno_eff ERANGE), m0, [].
  split; [apply getcwd_admits; left; reflexivity | vm_compute; reflexivity].
Qed.

(* -------------------------------------------------------------------------
   The step level: the subset lemma's negative twin
   ------------------------------------------------------------------------- *)

Lemma getcwd_step_from : forall e,
  In e (ERANGE :: getcwd_errnos) ->
  sstep [] (mkCfg getcwd_ms m0) []
    (SNext (mkCfg (advance_past_svc (apply_effect getcwd_ms (errno_eff e))) m0)).
Proof.
  intros e Hin.
  apply (sstep_syscall [] getcwd_ms m0 (Z_to_bv 64 17) (errno_eff e) m0 m0 []).
  - reflexivity.
  - reflexivity.
  - apply getcwd_admits. exact Hin.
  - reflexivity.
  - apply materialize_model_accesses_no_lazy. reflexivity.
Qed.

(** [Run.sstep] admits the -ENOMEM step. *)
Example getcwd_enomem_step_admitted :
  sstep [] (mkCfg getcwd_ms m0) []
    (SNext (mkCfg (advance_past_svc (apply_effect getcwd_ms (errno_eff ENOMEM))) m0)).
Proof. apply getcwd_step_from. right. left. reflexivity. Qed.

(** ... [Run.sstep_cfg Run.forced_only_cfg] refuses it.  Any step into
    that configuration is a syscall step whose outcome set a0 to
    -ENOMEM, and [getcwd_only] says such an outcome is one of the
    injected three — spurious, since -ERANGE was available — while the
    one non-spurious outcome, -ERANGE, lands in a different
    configuration. *)
Example getcwd_enomem_step_refused :
  ~ sstep_cfg [] forced_only_cfg (mkCfg getcwd_ms m0) []
      (SNext (mkCfg (advance_past_svc (apply_effect getcwd_ms (errno_eff ENOMEM))) m0)).
Proof.
  intros H.
  (* the exit step is refuted by [inversion] itself: it emits an exit
     event and this step emits nothing *)
  inversion H; subst;
    repeat match goal with
           | [ Hsvc : ms_svc_pending getcwd_ms = _ |- _ ] =>
               change (ms_svc_pending getcwd_ms) with (Some (Z_to_bv 64 17)) in Hsvc
           end.
  - (* an instruction step: a syscall is pending here *)
    discriminate.
  - (* a syscall step *)
    match goal with
    | [ Hsvc : Some _ = Some ?x8 |- _ ] => injection Hsvc as Hx8; subst x8
    end.
    match goal with
    | [ Hspec : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
        destruct (getcwd_only _ _ _ _ Hspec) as (Hm & Hevs & e & Hin & Heff); subst
    end.
    destruct Hin as [<- | Hin].
    + (* -ERANGE lands elsewhere: a0 differs *)
      match goal with
      | [ Hret : eff_ret _ = errno_ret _ |- _ ] =>
          apply (f_equal bv_unsigned) in Hret; vm_compute in Hret; discriminate Hret
      end.
    + (* an injected errno: spurious, which the step's premise refutes *)
      match goal with
      | [ Hns : ~ spurious_refusal_cfg _ _ _ _ |- _ ] => apply Hns
      end.
      split; [exact getcwd_off_under_forced_only |].
      split.
      * destruct Hin as [<- | [<- | [<- | []]]]; vm_compute; reflexivity.
      * exists (errno_eff ERANGE), m0, []. split.
        { apply getcwd_admits. left. reflexivity. }
        { vm_compute. reflexivity. }
Qed.

(** The positive twin: the filtered relation still steps here, on the
    answer the state determines. *)
Example getcwd_erange_step_admitted_under_forced_only :
  sstep_cfg [] forced_only_cfg (mkCfg getcwd_ms m0) []
    (SNext (mkCfg (advance_past_svc (apply_effect getcwd_ms (errno_eff ERANGE))) m0)).
Proof.
  apply (sstep_cfg_syscall [] forced_only_cfg getcwd_ms m0 (Z_to_bv 64 17)
           (errno_eff ERANGE) m0 m0 []).
  - reflexivity.
  - reflexivity.
  - apply getcwd_admits. left. reflexivity.
  - exact getcwd_erange_kept_under_forced_only.
  - reflexivity.
  - apply materialize_model_accesses_no_lazy. reflexivity.
Qed.

(* =========================================================================
   PART 4 — cred: setsid, forced by state
   ========================================================================= *)

Definition setsid_i : SyscallInput :=
  mkInput 157 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

Lemma setsid_dispatch : forall m o,
  syscall_spec setsid_i m o <-> setsid_spec setsid_i m o.
Proof.
  intros m o. unfold syscall_spec, dispatch.
  assert (E : bv_unsigned (in_sysno setsid_i) = 157%Z) by (vm_compute; reflexivity).
  rewrite E. reflexivity.
Qed.

(** Before any success, -EPERM is spurious: the session can be made. *)
Example setsid_eperm_spurious_before_success :
  spurious_refusal_cfg forced_only_cfg setsid_i m0 (errno_eff EPERM).
Proof.
  split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |].
  exists (mkEffect 1 [] []), (with_setsid_succeeded (with_tid 1 m0)), [].
  split; [| vm_compute; reflexivity].
  apply check_syscall_sound_ok. check_eq.
Qed.

(** After one, -EPERM is the only answer and is kept: the state forces
    it. *)
Example setsid_eperm_forced_after_success :
  ~ spurious_refusal_cfg forced_only_cfg setsid_i (with_setsid_succeeded m0) (errno_eff EPERM).
Proof.
  intros (_ & _ & (eff' & m' & evs' & Hspec & Hnr)).
  apply (proj1 (setsid_dispatch _ _)) in Hspec.
  unfold setsid_spec, bind, get_model in Hspec. sys_destruct.
  assert (Hs : m_setsid_succeeded (with_setsid_succeeded m0) = true) by reflexivity.
  rewrite Hs in *.
  unfold err_ret, ret_only, pure in *. sys_destruct.
  vm_compute in Hnr. discriminate Hnr.
Qed.

(* =========================================================================
   PART 5 — alloc: mmap, forced by the budget; and the argument gate
   ========================================================================= *)

Lemma mmap_dispatch : forall i m o,
  bv_unsigned (in_sysno i) = 222%Z ->
  syscall_spec i m o
  <-> mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4)
                (in_arg i 5) i m o.
Proof.
  intros i m o E. unfold syscall_spec, dispatch. rewrite E. reflexivity.
Qed.

(** Within budget the -ENOMEM is spurious: the grant
    [Checks.Cases.Mm.Mmap.mmap_within_budget_grants] admits is the
    non-refusal answer. *)
Example mmap_enomem_spurious_within_budget :
  spurious_refusal_cfg forced_only_cfg (mmap_in 4096) tight_model (errno_eff ENOMEM).
Proof.
  split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |].
  exists (mkEffect 131072 [] [(131072, 4096)]),
    (with_vmmaps (mkVmMaps [] [(131072, 4096); (65536, 4096)] 0 0 8192) tight_model), [].
  split; [| vm_compute; reflexivity].
  apply check_syscall_sound_ok. exact mmap_within_budget_grants.
Qed.

(** Beyond it the -ENOMEM is FORCED and kept: the grant's [choose]
    carries the budget test in its predicate, and that test is false, so
    the errno arm is the only one with an inhabitant. *)
Example mmap_enomem_forced_beyond_budget :
  ~ spurious_refusal_cfg forced_only_cfg (mmap_in 8192) tight_model (errno_eff ENOMEM).
Proof.
  intros (_ & _ & (eff' & m' & evs' & Hspec & Hnr)).
  apply (proj1 (mmap_dispatch (mmap_in 8192) _ _ ltac:(vm_compute; reflexivity))) in Hspec.
  unfold mmap_spec in Hspec.
  revert Hspec.
  destruct (negb (mmap_off_aligned_b (in_arg (mmap_in 8192) 5))) eqn:E0a;
    [vm_compute in E0a; discriminate E0a |].
  destruct (negb (mmap_anon_b (in_arg (mmap_in 8192) 3))) eqn:E0b;
    [vm_compute in E0b; discriminate E0b |].
  destruct (w_is0 (in_arg (mmap_in 8192) 1)) eqn:E1; [vm_compute in E1; discriminate E1 |].
  destruct (mmap_modeled_b (in_arg (mmap_in 8192) 2) (in_arg (mmap_in 8192) 3)
              (in_arg (mmap_in 8192) 5)) eqn:E2;
    [| vm_compute in E2; discriminate E2].
  intros Hspec.
  unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, get_model, modify in Hspec.
  cbv beta zeta in Hspec.
  sys_destruct.
  - (* the errno arm: a refusal, which [Hnr] denies *)
    match goal with
    | [ Hin : In ?e mmap_errnos |- _ ] =>
        destruct Hin as [<- | []]
    end.
    vm_compute in Hnr. discriminate Hnr.
  - (* the grant: its budget conjunct is false here *)
    match goal with
    | [ Hb : mmap_noreserve_backed_ok _ _ _ = true |- _ ] =>
        vm_compute in Hb; discriminate Hb
    end.
Qed.

(** An -ENOMEM the ARGUMENT GATE determines is kept although -ENOMEM is
    the one member of [Mmap.mmap_errnos]: at this input the gate's
    [err_ret ENOMEM] is the whole spec, so no non-refusal outcome
    exists and the filter has nothing to remove.  This is the exactness
    claim of [Run.v]'s spurious-failure header at the one place a
    list-driven filter would have got it wrong. *)
Definition mmap_overflow_i : SyscallInput :=
  mkInput 222 [4097; 18446744073709551615; 0; 50; mmap_fd_none; 0]
    (fun _ => None) (fun _ => None).

Example mmap_gate_enomem_kept_under_forced_only :
  ~ spurious_refusal_cfg forced_only_cfg mmap_overflow_i noaccess_base (errno_eff ENOMEM).
Proof.
  intros (_ & _ & (eff' & m' & evs' & Hspec & Hnr)).
  apply (proj1 (mmap_dispatch mmap_overflow_i _ _ ltac:(vm_compute; reflexivity))) in Hspec.
  unfold mmap_spec in Hspec.
  revert Hspec.
  destruct (negb (mmap_off_aligned_b (in_arg mmap_overflow_i 5))) eqn:E0a;
    [vm_compute in E0a; discriminate E0a |].
  destruct (negb (mmap_anon_b (in_arg mmap_overflow_i 3))) eqn:E0b;
    [vm_compute in E0b; discriminate E0b |].
  destruct (w_is0 (in_arg mmap_overflow_i 1)) eqn:E1; [vm_compute in E1; discriminate E1 |].
  destruct (mmap_modeled_b (in_arg mmap_overflow_i 2) (in_arg mmap_overflow_i 3)
              (in_arg mmap_overflow_i 5)) eqn:E2;
    [vm_compute in E2; discriminate E2 |].
  destruct (mmap_noaccess_b (in_arg mmap_overflow_i 2) (in_arg mmap_overflow_i 3)
              (in_arg mmap_overflow_i 5)) eqn:E3;
    [vm_compute in E3; discriminate E3 |].
  destruct (mmap_fixed_noaccess_b (in_arg mmap_overflow_i 2) (in_arg mmap_overflow_i 3)
              (in_arg mmap_overflow_i 5)) eqn:E4;
    [| vm_compute in E4; discriminate E4].
  cbv zeta.
  destruct (two_pow_64 <=? bv_unsigned (in_arg mmap_overflow_i 0)
              + page_round_up_Z (bv_unsigned (in_arg mmap_overflow_i 1)))%Z eqn:E5;
    [| vm_compute in E5; discriminate E5].
  intros Hspec.
  unfold err_ret, ret_only, pure in Hspec. sys_destruct.
  vm_compute in Hnr. discriminate Hnr.
Qed.

(* =========================================================================
   PART 6 — run level: the two witnesses, at the other reading
   ========================================================================= *)

(** [Checks.Examples.exits_c] is sound for the filtered predicate too,
    under every configuration — the same proof as
    [Checks.Examples.exits_c_must_exit_at], over [Run.sstep_cfg]: the
    instruction steps and the exit step carry no filter premise, and the
    two syscall shapes the filter does touch are ruled out at an exit
    ecall by the exit-dispatch lemmas exactly as before. *)
Lemma exits_c_must_exit_at_cfg : forall cfg segs code fuel ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  exits_c segs code fuel ms = true ->
  must_exit_at_cfg cfg segs code (mkCfg ms model).
Proof.
  intros cfg segs code fuel. induction fuel as [|fuel IH]; intros ms model Hh Hlazy Hc;
    [discriminate|].
  cbn [exits_c] in Hc.
  destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
  - (* the terminating ecall *)
    apply andb_true_iff in Hc as [Hx8 Hcode].
    apply bv_eqb_eq in Hcode.
    assert (Hno : exit_sysno (in_sysno (sys_input segs ms x8))).
    { cbn [in_sysno sys_input].
      apply orb_true_iff in Hx8. destruct Hx8 as [H|H]; apply Z.eqb_eq in H;
        [left|right]; exact H. }
    assert (Harg : in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0) by reflexivity.
    set (m' := with_halted (bv_and (in_arg (sys_input segs ms x8) 0)
                                   (Z_to_bv 64 255)) model).
    apply must_exit_at_cfg_running.
    + cbn [cfg_model]. exact Hh.
    + exists ([] ++ [ExitEv (bv_and (in_arg (sys_input segs ms x8) 0)
                                    (Z_to_bv 64 255)) (m_fs m')]),
        (SNext (mkCfg ms m')).
      eapply sstep_cfg_exit; [exact Hh | exact Hsvc | | | ].
      * subst m'. exact (exit_dispatch_admits _ model Hno).
      * subst m'. reflexivity.
      * subst m'. apply m_killed_with_halted.
    + intros evs Hss. inversion Hss; subst; try congruence; unify_svc x8.
      * match goal with
        | [ H : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
            pose proof (exit_dispatch_halts _ _ _ _ _ Hno H) as Hhalts
        end.
        congruence.
      * match goal with
        | [ H : syscall_spec _ _ Unmodeled |- _ ] =>
            exact (exit_dispatch_modeled _ _ Hno H)
        end.
    + intros evs c' Hss. inversion Hss; subst; try congruence; unify_svc x8.
      * match goal with
        | [ H : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
            pose proof (exit_dispatch_halts _ _ _ _ _ Hno H) as Hhalts
        end.
        congruence.
      * match goal with
        | [ H : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
            pose proof (exit_dispatch_halts _ _ _ _ _ Hno H) as Hhalts
        end.
        apply must_exit_at_cfg_halted; cbn [cfg_model].
        -- rewrite Hhalts, Harg. reflexivity.
        -- match goal with
           | [ H : m_killed ?m' = None |- m_killed ?m' = None ] => exact H
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
    assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
    { rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity. }
    apply must_exit_at_cfg_running.
    + cbn [cfg_model]. exact Hh.
    + exists [], (SNext (mkCfg ms' model)).
      eapply sstep_cfg_instr; eassumption.
    + intros evs Hss. inversion Hss; subst; congruence.
    + intros evs c' Hss. inversion Hss; subst; try congruence.
      match goal with
      | [ H : mi_account_step _ _ _ = MachineOk (?a, ?b) |- _ ] =>
          rewrite Hacc in H; injection H as -> ->
      end.
      apply IH; assumption.
Qed.

(** The exit-0 image must-exits under forced-only: the positive witness
    [MustExit]'s header points at, at the pinned reading. *)
Example exit0_image_must_exit_zero_under_forced_only :
  must_exit_with_scfg forced_only_cfg verdict_accept exit0_image demo_limit demo_entry
    (mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                       default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48).
Proof.
  cbn [must_exit_with_scfg exit0_image demo_entry]. unfold init_config.
  apply (exits_c_must_exit_at_cfg _ _ _ 8); [reflexivity | reflexivity |].
  vm_compute. reflexivity.
Qed.

(** ... and the undecodable image refutes it there too, at every code:
    the fetch that leaves the modeled surface is an instruction step, and
    the filter touches no instruction step.

    The stack pointer is [Cases.Prelude.demo_sp] and not the 65536 the
    older fixtures used, because the entry carries
    [Cases.Prelude.demo_draw], whose [StackLayout.ed_top] is one page
    above [demo_sp]: the entry image is EVERYTHING between the stack
    pointer and that top, so a lower pointer would ask the model to lay
    about 2^47 bytes.  The break is a different one from
    [Checks.Examples.demo_entry]'s on purpose — the refutation is about
    the fetch, not about any placement. *)
Example undecodable_image_refutes_must_exit_under_forced_only :
  ~ must_exit_with_scfg forced_only_cfg verdict_accept undecodable_image demo_limit
      (mkEntry demo_sp (Z_to_bv 64 1048576)
         (Z_to_bv 64 mmap_base_max) demo_draw)
      (mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                       default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48).
Proof.
  apply must_exit_with_scfg_refuted_by_error, run_scfg_unmodeled_errors.
  cbn [run_scfg bh_unmodeled undecodable_image]. unfold init_config.
  match goal with
  | |- reaches_unmodeled_cfg _ _ ?c => exists [], c
  end.
  split; [apply star_cfg_refl |].
  split; [reflexivity |]. left. split; [reflexivity |].
  cbn [cfg_ms cfg_model].
  match goal with
  | |- mi_account_step ?segs ?ms ?model = _ =>
      rewrite (mi_account_step_no_lazy segs ms model ltac:(reflexivity))
  end.
  cbn [mkProcInput in_argv in_envp in_uid in_hwcap].
  rewrite undecodable_step_unmodeled. reflexivity.
Qed.

(* =========================================================================
   PART 7 — munmap, faccessat2, getdents64: refusals no state forces
   ========================================================================= *)

(** Three arms inject a refusal beside an answer the model can always
    give instead: [munmap]'s -ENOMEM on a whole or a partial unmap
    ([Mmap.munmap_errnos], alloc), [faccessat2]'s -ENOMEM and -EACCES
    ([Open.faccessat_errnos], fs) and [getdents64]'s -ENOENT
    ([Readdir.getdents64_errnos], fs).
    For each, this part pins the family [Run.injected_table] gives it,
    that [Run.refusal_b] is exactly its list, and the claim no check on
    the table itself can make: wherever the spec admits one of these
    refusals, it admits a non-refusal at the same input and model.  So no
    state forces them, and a configuration that reads the family as
    forced-only removes every one ([unforced_refusal_spurious]). *)

Lemma munmap_dispatch : forall i m o,
  bv_unsigned (in_sysno i) = 215%Z ->
  syscall_spec i m o <-> munmap_spec (in_arg i 0) (in_arg i 1) i m o.
Proof. intros i m o E. unfold syscall_spec, dispatch. rewrite E. reflexivity. Qed.

Lemma faccessat2_dispatch : forall i m o,
  bv_unsigned (in_sysno i) = 439%Z ->
  syscall_spec i m o
  <-> faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. intros i m o E. unfold syscall_spec, dispatch. rewrite E. reflexivity. Qed.

Lemma getdents64_dispatch : forall i m o,
  bv_unsigned (in_sysno i) = 61%Z ->
  syscall_spec i m o <-> getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i m o.
Proof. intros i m o E. unfold syscall_spec, dispatch. rewrite E. reflexivity. Qed.

(** The family each arm is read under, at every configuration. *)
Lemma munmap_family_off : forall cfg i,
  bv_unsigned (in_sysno i) = 215%Z ->
  injected_family_off cfg i = negb (sc_alloc cfg).
Proof. intros cfg i E. unfold injected_family_off. rewrite E. reflexivity. Qed.

Lemma faccessat2_family_off : forall cfg i,
  bv_unsigned (in_sysno i) = 439%Z ->
  injected_family_off cfg i = negb (sc_fs cfg).
Proof. intros cfg i E. unfold injected_family_off. rewrite E. reflexivity. Qed.

Lemma getdents64_family_off : forall cfg i,
  bv_unsigned (in_sysno i) = 61%Z ->
  injected_family_off cfg i = negb (sc_fs cfg).
Proof. intros cfg i E. unfold injected_family_off. rewrite E. reflexivity. Qed.

(** The refusals of each arm are exactly its list. *)
Lemma munmap_refusal_b : forall i m r,
  bv_unsigned (in_sysno i) = 215%Z ->
  refusal_b i m r = ret_in_errnos munmap_errnos r.
Proof. intros i m r E. unfold refusal_b. rewrite E. reflexivity. Qed.

Lemma faccessat2_refusal_b : forall i m r,
  bv_unsigned (in_sysno i) = 439%Z ->
  refusal_b i m r = ret_in_errnos faccessat_errnos r.
Proof. intros i m r E. unfold refusal_b. rewrite E. reflexivity. Qed.

Lemma getdents64_refusal_b : forall i m r,
  bv_unsigned (in_sysno i) = 61%Z ->
  refusal_b i m r = ret_in_errnos getdents64_errnos r.
Proof. intros i m r E. unfold refusal_b. rewrite E. reflexivity. Qed.

(* -------------------------------------------------------------------------
   The spec level: a non-refusal beside every refusal
   ------------------------------------------------------------------------- *)

Local Lemma get_vmmaps_bind_ok_inv {A : Type} : forall (k : VmMaps -> Sys A)
    i m x m' evs,
  bind get_vmmaps k i m (Ok x m' evs) -> k (m_vmmaps m) i m (Ok x m' evs).
Proof.
  intros k i m x m' evs H.
  destruct H as (v & m1 & evs1 & evs2 & Hg & Hk & ->).
  unfold get_vmmaps in Hg. injection Hg as -> -> ->. exact Hk.
Qed.

(** Case on the first [if] of the spec in [H], in [H] and in the goal
    together: the goal is the same spec at another outcome. *)
Local Ltac case_if H :=
  match type of H with
  | context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E
  end;
  cbv iota in H |- *.

(** [H] says the spec gave one fixed answer and changed nothing, [Hr]
    that the answer is a refusal: they disagree by computation. *)
Local Ltac refute_ret H Hr :=
  exfalso; unfold err_ret, ret_only, pure in H;
  let Heff := fresh "Heff" in
  injection H as Heff _ _; subst; cbn [eff_ret] in Hr; vm_compute in Hr;
  discriminate Hr.

Local Ltac refute_unmodeled H :=
  exfalso; unfold unmodeled in H; discriminate H.

(** [munmap]: an -ENOMEM is admitted by the exact arm and by the
    partial arm, and each of them admits the cut beside it. *)
Lemma munmap_success_beside_refusal : forall a l i m eff m' evs,
  munmap_spec a l i m (Ok eff m' evs) ->
  ret_in_errnos munmap_errnos (eff_ret eff) = true ->
  munmap_spec a l i m
    (Ok (mkEffectU (Z_to_bv 64 0) [] []
           [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned l)))] [] [])
        (with_mmap_destroyed a (Z_to_bv 64 (page_round_up_Z (bv_unsigned l)))
           (mmap_fixed_destroyed_next (m_vmmaps m) a
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned l)))) m)
        []).
Proof.
  intros a l i m eff m' evs H Hr.
  unfold munmap_spec in H |- *.
  (* the argument gate: -EINVAL *)
  case_if H; [refute_ret H Hr |].
  apply get_vmmaps_bind_ok_inv in H. cbv beta zeta in H.
  eapply bind_ok0; [apply get_vmmaps_ok |]. cbv beta zeta.
  (* the range leaves the address space: -EINVAL *)
  case_if H; [refute_ret H Hr |].
  (* exactly one recorded mapping: the -ENOMEM beside the cut *)
  case_if H.
  { unfold with_mmap_destroyed, set_vmmaps, forget_vm_range.
    apply alt_r. eapply bind_ok0; [apply modify_ok |].
    eapply bind_ok0; [apply modify_ok |]. apply pure_ok. }
  (* nothing recorded in the range: 0 *)
  case_if H; [refute_ret H Hr |].
  (* the partial arm, or a decline *)
  case_if H; [| refute_unmodeled H].
  apply alt_r. eapply bind_ok0; [apply modify_ok |]. apply pure_ok.
Qed.

(** [faccessat2]: -ENOMEM and -EACCES are admitted only by
    [Fs.Open.access_exists_spec], which admits 0 beside them. *)
Lemma faccessat2_success_beside_refusal :
    forall dirfd pathp mode flags i m eff m' evs,
  faccessat2_spec dirfd pathp mode flags i m (Ok eff m' evs) ->
  ret_in_errnos faccessat_errnos (eff_ret eff) = true ->
  faccessat2_spec dirfd pathp mode flags i m
    (Ok (with_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
           (mkEffect (Z_to_bv 64 0) [] []))
        m []).
Proof.
  intros dirfd pathp mode flags i m eff m' evs H Hr.
  unfold faccessat2_spec in H |- *.
  apply input_bind_ok_inv in H. cbv beta in H.
  apply get_model_bind_ok_inv in H. cbv beta iota in H.
  eapply bind_ok0; [apply input_ok |]. cbv beta.
  eapply bind_ok0; [apply get_model_ok |]. cbv beta iota.
  (* the mode and flag gates: two -EINVALs, then two declines *)
  case_if H; [refute_ret H Hr |].
  case_if H; [refute_ret H Hr |].
  case_if H; [refute_unmodeled H |].
  case_if H; [refute_unmodeled H |].
  (* the pathname copy-in, around the body faccessat shares *)
  apply record_copyins_ok_inv in H. destruct H as (core & Hcore & ->).
  cbn [eff_ret with_copyins] in Hr.
  apply record_copyins_ok_empty; [reflexivity |].
  unfold faccessat_body_spec in Hcore |- *.
  destruct (read_cstr (in_mem i) pathp) as [p | |] eqn:Hcs;
    cbv iota in Hcore |- *; [| refute_ret Hcore Hr | refute_ret Hcore Hr].
  (* the empty pathname: -ENOENT *)
  case_if Hcore; [refute_ret Hcore Hr |].
  (* a dirfd other than AT_FDCWD: declined *)
  case_if Hcore; [refute_unmodeled Hcore |].
  (* "." and "..": the arm that can succeed *)
  case_if Hcore; [unfold access_exists_spec; apply alt_r; apply pure_ok |].
  case_if Hcore; [unfold access_exists_spec; apply alt_r; apply pure_ok |].
  (* a slash, an over-long name, an implied directory: declined *)
  case_if Hcore; [refute_unmodeled Hcore |].
  case_if Hcore; [refute_unmodeled Hcore |].
  case_if Hcore; [refute_unmodeled Hcore |].
  (* a present name: the arm that can succeed; an absent one: -ENOENT *)
  match type of Hcore with
  | context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:Hlk
  end;
  cbv iota in Hcore |- *.
  - unfold access_exists_spec. apply alt_r. apply pure_ok.
  - refute_ret Hcore Hr.
Qed.

(** [getdents64]: -ENOENT is admitted only on a directory whose buffer
    has no room for an entry, beside [filldir64]'s own -EINVAL. *)
Lemma getdents64_answer_beside_refusal : forall fd count i m eff m' evs,
  getdents64_spec fd count i m (Ok eff m' evs) ->
  ret_in_errnos getdents64_errnos (eff_ret eff) = true ->
  getdents64_spec fd count i m (Ok (mkEffect (errno_ret EINVAL) [] []) m []).
Proof.
  intros fd count i m eff m' evs H Hr.
  unfold getdents64_spec in H |- *.
  apply get_model_bind_ok_inv in H. cbv beta in H.
  eapply bind_ok0; [apply get_model_ok |]. cbv beta.
  match type of H with
  | context [match ?x with Some _ => _ | None => _ end] => destruct x as [e |] eqn:Hfd
  end;
  cbv iota in H |- *; [| refute_ret H Hr].
  (* every descriptor but a directory: -ENOTDIR *)
  destruct e; cbv iota in H |- *; try (refute_ret H Hr).
  (* the directory: no room for an entry, or a decline *)
  case_if H; [apply alt_r; apply pure_ok | refute_unmodeled H].
Qed.

(* -------------------------------------------------------------------------
   The syscall level
   ------------------------------------------------------------------------- *)

Lemma munmap_refusal_avoidable : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 215%Z ->
  syscall_spec i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = true ->
  exists eff' m'' evs',
    syscall_spec i m (Ok eff' m'' evs') /\ refusal_b i m (eff_ret eff') = false.
Proof.
  intros i m eff m' evs E Hspec Hr.
  rewrite (munmap_refusal_b _ _ _ E) in Hr.
  apply (munmap_dispatch _ _ _ E) in Hspec.
  pose proof (munmap_success_beside_refusal _ _ _ _ _ _ _ Hspec Hr) as Hw.
  do 3 eexists. split.
  - apply (munmap_dispatch _ _ _ E). exact Hw.
  - rewrite (munmap_refusal_b _ _ _ E). cbn [eff_ret]. vm_compute. reflexivity.
Qed.

Lemma faccessat2_refusal_avoidable : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 439%Z ->
  syscall_spec i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = true ->
  exists eff' m'' evs',
    syscall_spec i m (Ok eff' m'' evs') /\ refusal_b i m (eff_ret eff') = false.
Proof.
  intros i m eff m' evs E Hspec Hr.
  rewrite (faccessat2_refusal_b _ _ _ E) in Hr.
  apply (faccessat2_dispatch _ _ _ E) in Hspec.
  pose proof (faccessat2_success_beside_refusal _ _ _ _ _ _ _ _ _ Hspec Hr) as Hw.
  do 3 eexists. split.
  - apply (faccessat2_dispatch _ _ _ E). exact Hw.
  - rewrite (faccessat2_refusal_b _ _ _ E). cbn [eff_ret with_copyins].
    vm_compute. reflexivity.
Qed.

Lemma getdents64_refusal_avoidable : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 61%Z ->
  syscall_spec i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = true ->
  exists eff' m'' evs',
    syscall_spec i m (Ok eff' m'' evs') /\ refusal_b i m (eff_ret eff') = false.
Proof.
  intros i m eff m' evs E Hspec Hr.
  rewrite (getdents64_refusal_b _ _ _ E) in Hr.
  apply (getdents64_dispatch _ _ _ E) in Hspec.
  pose proof (getdents64_answer_beside_refusal _ _ _ _ _ _ _ Hspec Hr) as Hw.
  do 3 eexists. split.
  - apply (getdents64_dispatch _ _ _ E). exact Hw.
  - rewrite (getdents64_refusal_b _ _ _ E). cbn [eff_ret]. vm_compute. reflexivity.
Qed.

(** THE CLAIM: for these three numbers, under any configuration that
    reads the arm's family as forced-only, every refusal the spec admits
    is spurious — so [Run.sstep_cfg] takes none of them. *)
Theorem unforced_refusal_spurious : forall cfg i m eff m' evs,
  In (bv_unsigned (in_sysno i)) [61; 215; 439]%Z ->
  injected_family_off cfg i = true ->
  syscall_spec i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = true ->
  spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff m' evs Hno Hoff Hspec Hr.
  split; [exact Hoff |]. split; [exact Hr |].
  destruct Hno as [E | [E | [E | []]]]; symmetry in E.
  - exact (getdents64_refusal_avoidable _ _ _ _ _ E Hspec Hr).
  - exact (munmap_refusal_avoidable _ _ _ _ _ E Hspec Hr).
  - exact (faccessat2_refusal_avoidable _ _ _ _ _ E Hspec Hr).
Qed.

(** ... read as the premise [Run.sstep_cfg]'s syscall steps carry: an
    outcome the configured run keeps is not a refusal. *)
Corollary unforced_kept_outcome_not_refusal : forall cfg i m eff m' evs,
  In (bv_unsigned (in_sysno i)) [61; 215; 439]%Z ->
  injected_family_off cfg i = true ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg cfg i m eff ->
  refusal_b i m (eff_ret eff) = false.
Proof.
  intros cfg i m eff m' evs Hno Hoff Hspec Hns.
  destruct (refusal_b i m (eff_ret eff)) eqn:Hr; [| reflexivity].
  exfalso. exact (Hns (unforced_refusal_spurious _ _ _ _ _ _ Hno Hoff Hspec Hr)).
Qed.

(** The three named configurations.  Forced-only removes all three
    refusals. *)
Corollary unforced_refusal_spurious_forced_only : forall i m eff m' evs,
  In (bv_unsigned (in_sysno i)) [61; 215; 439]%Z ->
  syscall_spec i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = true ->
  spurious_refusal_cfg forced_only_cfg i m eff.
Proof.
  intros i m eff m' evs Hno Hspec Hr.
  apply (unforced_refusal_spurious _ _ _ _ m' evs Hno); [| exact Hspec | exact Hr].
  destruct Hno as [E | [E | [E | []]]]; symmetry in E.
  - rewrite (getdents64_family_off _ _ E). reflexivity.
  - rewrite (munmap_family_off _ _ E). reflexivity.
  - rewrite (faccessat2_family_off _ _ E). reflexivity.
Qed.

(** [alloc_only_cfg false] removes [munmap]'s -ENOMEM, which is not a
    budget refusal ([Run.alloc_budget_refused_munmap]) ... *)
Corollary munmap_refusal_spurious_alloc_only : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 215%Z ->
  syscall_spec i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = true ->
  spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m eff m' evs E Hspec Hr.
  apply (unforced_refusal_spurious _ _ _ _ m' evs); [| | exact Hspec | exact Hr].
  - rewrite E. cbn [In]. right. left. reflexivity.
  - rewrite (munmap_family_off _ _ E). reflexivity.
Qed.

(** ... and keeps the two fs refusals, as it keeps [getcwd]'s. *)
Corollary fs_refusals_kept_alloc_only : forall i m eff,
  In (bv_unsigned (in_sysno i)) [61; 439]%Z ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m eff Hno. apply spurious_refusal_family_on.
  destruct Hno as [E | [E | []]]; symmetry in E.
  - rewrite (getdents64_family_off _ _ E). reflexivity.
  - rewrite (faccessat2_family_off _ _ E). reflexivity.
Qed.

(* -------------------------------------------------------------------------
   Not vacuous: each arm admits its refusal, and there it is spurious
   ------------------------------------------------------------------------- *)

(** A hole punched in [Checks.Cases.Mm.Mmap.four_page_model]'s mapping,
    answered -ENOMEM ([Checks.Cases.Mm.Mmap.munmap_partial_enomem]). *)
Definition munmap_hole_i : SyscallInput :=
  mkInput 215 [69632; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

Example munmap_hole_enomem_admitted :
  syscall_spec munmap_hole_i four_page_model
    (Ok (errno_eff ENOMEM) four_page_model []).
Proof. apply check_syscall_sound_ok. check_eq. Qed.

Example munmap_hole_enomem_spurious_under_forced_only :
  spurious_refusal_cfg forced_only_cfg munmap_hole_i four_page_model
    (errno_eff ENOMEM).
Proof.
  apply (unforced_refusal_spurious_forced_only _ _ _ four_page_model []);
    [vm_compute; right; left; reflexivity
    | exact munmap_hole_enomem_admitted
    | vm_compute; reflexivity].
Qed.

Example munmap_hole_enomem_spurious_under_alloc_only :
  spurious_refusal_cfg (alloc_only_cfg false) munmap_hole_i four_page_model
    (errno_eff ENOMEM).
Proof.
  apply (munmap_refusal_spurious_alloc_only _ _ _ four_page_model []);
    [vm_compute; reflexivity
    | exact munmap_hole_enomem_admitted
    | vm_compute; reflexivity].
Qed.

Example munmap_hole_enomem_kept_under_may_fail :
  ~ spurious_refusal_cfg may_fail_cfg munmap_hole_i four_page_model
      (errno_eff ENOMEM).
Proof. apply spurious_refusal_may_fail. Qed.

(** The same for an unmap of ONE WHOLE mapping, the arm Linux answers
    -ENOMEM at in [do_vmi_align_munmap] (mm/vma.c, Linux v6.18.46):
    [Checks.Cases.Mm.Mmap.one_map_model]'s single mapping, unmapped
    whole ([Checks.Cases.Mm.Mmap.munmap_whole_mapping_enomem]).  Under
    may-fail the refusal stays; forced-only and [alloc_only_cfg false]
    both remove it, so neither of those two readings changes. *)
Definition munmap_whole_i : SyscallInput :=
  mkInput 215 [65536; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

Example munmap_whole_enomem_admitted :
  syscall_spec munmap_whole_i one_map_model
    (Ok (errno_eff ENOMEM) one_map_model []).
Proof. apply check_syscall_sound_ok. check_eq. Qed.

Example munmap_whole_enomem_spurious_under_forced_only :
  spurious_refusal_cfg forced_only_cfg munmap_whole_i one_map_model
    (errno_eff ENOMEM).
Proof.
  apply (unforced_refusal_spurious_forced_only _ _ _ one_map_model []);
    [vm_compute; right; left; reflexivity
    | exact munmap_whole_enomem_admitted
    | vm_compute; reflexivity].
Qed.

Example munmap_whole_enomem_spurious_under_alloc_only :
  spurious_refusal_cfg (alloc_only_cfg false) munmap_whole_i one_map_model
    (errno_eff ENOMEM).
Proof.
  apply (munmap_refusal_spurious_alloc_only _ _ _ one_map_model []);
    [vm_compute; reflexivity
    | exact munmap_whole_enomem_admitted
    | vm_compute; reflexivity].
Qed.

Example munmap_whole_enomem_kept_under_may_fail :
  ~ spurious_refusal_cfg may_fail_cfg munmap_whole_i one_map_model
      (errno_eff ENOMEM).
Proof. apply spurious_refusal_may_fail. Qed.

(** F_OK on the present name "a" of [Checks.Cases.Fs.Open.fa2_model],
    answered -ENOMEM. *)
Definition faccessat2_a_i : SyscallInput :=
  mkInput 439 [AT_FDCWD; 8192; 0; 0; 0; 0] fa_mem_name_a (fun _ => None).

Definition faccessat2_enomem_eff : SyscallEffect :=
  with_copyins [(8192, 2%nat)] (errno_eff ENOMEM).

Example faccessat2_a_enomem_admitted :
  syscall_spec faccessat2_a_i fa2_model (Ok faccessat2_enomem_eff fa2_model []).
Proof. apply check_syscall_sound_ok. check_eq. Qed.

Example faccessat2_a_enomem_spurious_under_forced_only :
  spurious_refusal_cfg forced_only_cfg faccessat2_a_i fa2_model faccessat2_enomem_eff.
Proof.
  apply (unforced_refusal_spurious_forced_only _ _ _ fa2_model []);
    [vm_compute; right; right; left; reflexivity
    | exact faccessat2_a_enomem_admitted
    | vm_compute; reflexivity].
Qed.

Example faccessat2_a_enomem_kept_under_alloc_only :
  ~ spurious_refusal_cfg (alloc_only_cfg false) faccessat2_a_i fa2_model
      faccessat2_enomem_eff.
Proof. apply fs_refusals_kept_alloc_only. vm_compute. right. left. reflexivity. Qed.

(** A directory read into a zero-byte buffer
    ([Checks.Cases.Fs.Readdir.getdents64_answers_are_inert]), answered
    -ENOENT. *)
Example getdents64_dir_enoent_admitted :
  syscall_spec (getdents64_in 5 0) getdents64_model
    (Ok (errno_eff ENOENT) getdents64_model []).
Proof. apply check_syscall_sound_ok. check_eq. Qed.

Example getdents64_dir_enoent_spurious_under_forced_only :
  spurious_refusal_cfg forced_only_cfg (getdents64_in 5 0) getdents64_model
    (errno_eff ENOENT).
Proof.
  apply (unforced_refusal_spurious_forced_only _ _ _ getdents64_model []);
    [vm_compute; left; reflexivity
    | exact getdents64_dir_enoent_admitted
    | vm_compute; reflexivity].
Qed.

Example getdents64_dir_enoent_kept_under_alloc_only :
  ~ spurious_refusal_cfg (alloc_only_cfg false) (getdents64_in 5 0)
      getdents64_model (errno_eff ENOENT).
Proof. apply fs_refusals_kept_alloc_only. vm_compute. left. reflexivity. Qed.

(** A WRITE INTO AN EMPTY PIPE, answered -ENOMEM: the page
    [anon_pipe_get_page] (fs/pipe.c, Linux v6.18.46) could not get.
    [Checks.Cases.Fs.ReadWrite.pipe_write_into_an_empty_pipe_may_be_enomem]
    is the arm; this is what the two readings do with it.

    IT IS NEVER FORCED, and here that is not an argument about states
    but a fact about the arm's shape: [ReadWrite.write_spec] offers the
    errno under an [alt] whose other side is the delivery, so wherever
    the spec admits this refusal it admits the delivery at the same
    input and model.  The third conjunct of
    [spurious_refusal_cfg] is therefore discharged by exhibiting that
    delivery, which is what the proof below does, rather than through
    [unforced_refusal_spurious] — that theorem is stated over the three
    numbers whose avoidability needed a lemma each.

    SO THE TWO READINGS PART HERE, and a task has to know which it is
    using.  [forced_only_cfg] reads the fs family as forced-only and
    removes this answer; [alloc_only_cfg false] — the reading most
    statements in this tree use — switches only the ALLOCATION family
    and leaves fs at may-fail, so it KEEPS it, exactly as it keeps
    [getdents64]'s -ENOENT and [faccessat2]'s -ENOMEM.  The family is
    fs rather than alloc because [Run.injected_table]'s allocation
    family is the one whose forcing condition is the MODEL's own budget
    ([State.source_alloc_limit] and the marks beside it), and a pipe's
    page is not drawn against that budget.

    BEING KEPT UNDER THE ALLOC READING IS THE RIGHT CONSEQUENCE AND NOT
    A COST TO AVOID, which is the question a reader asks here next.
    [alloc_only_cfg false] says a MEMORY REQUEST fails only where the
    state forces it; this refusal is not a memory request of the
    program at all — the program asked to write bytes, and the page is
    one the kernel takes for its own pipe buffer — so that reading has
    nothing to say about it and leaves it where may-fail put it. *)
Definition write_pipe_enomem_i : SyscallInput :=
  mkInput 64 [4; 4096; 2; 0; 0; 0] mem_ab (fun _ => None).

Example write_pipe_enomem_admitted :
  syscall_spec write_pipe_enomem_i pipe_empty_model
    (Ok (errno_eff ENOMEM) pipe_empty_model []).
Proof. apply check_syscall_sound_ok. check_eq. Qed.

Example write_pipe_delivery_admitted_beside_it :
  syscall_spec write_pipe_enomem_i pipe_empty_model
    (Ok (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
       (with_pipes [(0, ([97; 98], 2%Z))] pipe_empty_model) []).
Proof. apply check_syscall_sound_ok. check_eq. Qed.

Example write_pipe_enomem_spurious_under_forced_only :
  spurious_refusal_cfg forced_only_cfg write_pipe_enomem_i pipe_empty_model
    (errno_eff ENOMEM).
Proof.
  split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |].
  exists (with_copyins [(4096, 2%nat)] (mkEffect 2 [] [])),
         (with_pipes [(0, ([97; 98], 2%Z))] pipe_empty_model), [].
  split; [exact write_pipe_delivery_admitted_beside_it | vm_compute; reflexivity].
Qed.

Example write_pipe_enomem_kept_under_alloc_only :
  ~ spurious_refusal_cfg (alloc_only_cfg false) write_pipe_enomem_i
      pipe_empty_model (errno_eff ENOMEM).
Proof. apply spurious_refusal_family_on. vm_compute. reflexivity. Qed.

Example write_pipe_enomem_kept_under_may_fail :
  ~ spurious_refusal_cfg may_fail_cfg write_pipe_enomem_i pipe_empty_model
      (errno_eff ENOMEM).
Proof. apply spurious_refusal_may_fail. Qed.
