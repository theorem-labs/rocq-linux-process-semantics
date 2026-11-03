(** * LinuxProcessSem.Checks.MmapTopFrame — the memory calls keep [mmap_top]

    Not part of the trusted specification: one fact about every [Ok]
    outcome [Specs.syscall_spec] admits for the six calls that write the
    mapping ledger or its backing: mmap (222), munmap (215), mremap
    (216), brk (214), mprotect (226) and madvise (233).

    [State.mmap_top] is the top of Linux's top-down search window.  It
    reads only two fields of the ledger, [vm_mmap_base] and
    [vm_init_sp] (through [State.alloc_top]), and the field notes in
    [State.VmMaps] call both IMMUTABLE for the run.  This file checks
    that claim against the checker of each call: every post-model those
    arms build keeps both fields, so the window top after the call is
    the one before it.  A consumer that bounds where a NULL-hint grant
    lands ([Common.AsanWindow.family_place_in_window]) measures its
    window from [mmap_top], and this is why the window does not move
    from one call to the next.

    The refusal arms ([CheckOk m []]) keep the model whole, so they keep
    the fields too.  That includes the -ENOMEM arm of munmap: a failed
    munmap changes no ledger entry
    ([Checks.SpuriousCfg.munmap_whole_enomem_admitted]).

    Each arm is walked through its checker, as [Checks.MmStepFrame]
    does for [m_halted]. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
Import ListNotations.

(** The two fields [mmap_top] reads. *)
Definition top_fields_kept (h h' : VmMaps) : Prop :=
  vm_mmap_base h' = vm_mmap_base h /\ vm_init_sp h' = vm_init_sp h.

(** [mmap_top] depends only on [vm_mmap_base] and [vm_init_sp]. *)
Lemma mmap_top_of_top_fields : forall h h',
  top_fields_kept h h' -> mmap_top h' = mmap_top h.
Proof.
  intros h h' [Hb Hs]. unfold mmap_top, alloc_top. rewrite Hb, Hs. reflexivity.
Qed.

(* -------------------------------------------------------------------------
   The post-model wrappers keep the ledger, or replace it by a named writer
   ------------------------------------------------------------------------- *)

Lemma m_vmmaps_forget_vm_ranges : forall rs m,
  m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma m_vmmaps_with_brk_next : forall m req r,
  m_vmmaps (with_brk_next m req r) = brk_model_next (m_vmmaps m) req r.
Proof.
  intros m req r. unfold with_brk_next. cbv zeta.
  rewrite m_vmmaps_forget_vm_ranges. reflexivity.
Qed.

Lemma m_vmmaps_with_mmap_backing : forall flags a n m,
  m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof.
  intros flags a n m. unfold with_mmap_backing.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.

Lemma m_vmmaps_with_mmap_replacement : forall flags a n m,
  m_vmmaps (with_mmap_replacement flags a n m) = m_vmmaps m.
Proof.
  intros flags a n m. unfold with_mmap_replacement.
  rewrite m_vmmaps_with_mmap_backing. reflexivity.
Qed.

(* -------------------------------------------------------------------------
   The checkers
   ------------------------------------------------------------------------- *)

(** Split [H] on every [if] and [match] until it is a leaf: a
    [CheckOk _ _ = CheckOk _ _] for the caller, or a refusal that
    [discriminate] closes.  The same tactic as [Checks.MmStepFrame]'s. *)
Local Ltac walk H :=
  repeat (cbv beta iota zeta in H;
          lazymatch type of H with
          | CheckOk _ _ = CheckOk _ _ => fail
          | _ => match type of H with
                 | context [match ?x with _ => _ end] => destruct x
                 end
          end);
  try discriminate H.

(** At a leaf, the post-model is [m], or a wrapper over [with_vmmaps]
    of a writer that copies [vm_mmap_base] and [vm_init_sp] from the
    pre-ledger. *)
Local Ltac leaf H :=
  injection H as <- <-; unfold top_fields_kept;
  rewrite ?m_vmmaps_with_mmap_backing, ?m_vmmaps_with_mmap_replacement,
          ?m_vmmaps_with_brk_next;
  split; reflexivity.

Lemma check_mmap_top_frame : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  top_fields_kept (m_vmmaps m) (m_vmmaps m').
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H.
  unfold check_mmap, check_ret_only in H. walk H. all: leaf H.
Qed.

Lemma check_munmap_top_frame : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs ->
  top_fields_kept (m_vmmaps m) (m_vmmaps m').
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H.
  unfold check_munmap, check_ret_only in H. walk H. all: leaf H.
Qed.

Lemma check_mremap_top_frame : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs ->
  top_fields_kept (m_vmmaps m) (m_vmmaps m').
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H.
  unfold check_mremap, check_ret_only in H. walk H. all: leaf H.
Qed.

Lemma check_brk_top_frame : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs ->
  top_fields_kept (m_vmmaps m) (m_vmmaps m').
Proof.
  intros req [ret ws zs us cs ci] m m' evs H.
  unfold check_brk in H. walk H. all: leaf H.
Qed.

Lemma check_mprotect_top_frame : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  top_fields_kept (m_vmmaps m) (m_vmmaps m').
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H.
  unfold check_mprotect, check_ret_only in H. walk H. all: leaf H.
Qed.

Lemma check_madvise_top_frame : forall addr len advice eff m m' evs,
  check_madvise addr len advice eff m = CheckOk m' evs ->
  top_fields_kept (m_vmmaps m) (m_vmmaps m').
Proof.
  intros addr len advice [ret ws zs us cs ci] m m' evs H.
  unfold check_madvise, check_ret_only in H. walk H. all: leaf H.
Qed.

(* -------------------------------------------------------------------------
   Through the dispatcher
   ------------------------------------------------------------------------- *)

(** The calls this file covers, by number. *)
Definition ledger_calls : list Z := [222; 215; 216; 214; 226; 233]%Z.

Theorem mm_ok_keeps_top_fields : forall i m eff m' evs,
  In (bv_unsigned (in_sysno i)) ledger_calls ->
  syscall_spec i m (Ok eff m' evs) ->
  top_fields_kept (m_vmmaps m) (m_vmmaps m').
Proof.
  intros i m eff m' evs Hin Hspec.
  apply check_syscall_complete_ok in Hspec.
  unfold ledger_calls in Hin.
  destruct Hin as [E | [E | [E | [E | [E | [E | []]]]]]]; symmetry in E.
  - rewrite (check_syscall_mmap i eff m E) in Hspec.
    exact (check_mmap_top_frame _ _ _ _ _ _ _ _ _ _ Hspec).
  - rewrite (check_syscall_munmap i eff m E) in Hspec.
    exact (check_munmap_top_frame _ _ _ _ _ _ Hspec).
  - rewrite (check_syscall_mremap i eff m E) in Hspec.
    exact (check_mremap_top_frame _ _ _ _ _ _ _ _ Hspec).
  - rewrite (check_syscall_brk i eff m E) in Hspec.
    exact (check_brk_top_frame _ _ _ _ _ Hspec).
  - rewrite (check_syscall_mprotect i eff m E) in Hspec.
    exact (check_mprotect_top_frame _ _ _ _ _ _ _ Hspec).
  - rewrite (check_syscall_madvise i eff m E) in Hspec.
    exact (check_madvise_top_frame _ _ _ _ _ _ _ Hspec).
Qed.

(** THE FRAME.  After any [Ok] outcome of the six calls, the top of the
    top-down search window is the one before the call. *)
Theorem mm_ok_keeps_mmap_top : forall i m eff m' evs,
  In (bv_unsigned (in_sysno i)) ledger_calls ->
  syscall_spec i m (Ok eff m' evs) ->
  mmap_top (m_vmmaps m') = mmap_top (m_vmmaps m).
Proof.
  intros i m eff m' evs Hin Hspec.
  exact (mmap_top_of_top_fields _ _ (mm_ok_keeps_top_fields i m eff m' evs Hin Hspec)).
Qed.
