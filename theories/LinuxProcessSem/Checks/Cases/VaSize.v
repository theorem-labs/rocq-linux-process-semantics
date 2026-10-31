(** * LinuxProcessSem.Checks.Cases.VaSize — the declared address-space size, instance by instance

    Mirrors the [State.VaSize] block of [State.v] and the per-size entry
    predicates of [Run.v].  The declaration is a value of the input, so
    what there is to pin is (i) that the [Sv48] instance is the literal
    constants the rest of the tree was written against, derived rather
    than copied; (ii) that a wrong declaration is refused for the RIGHT
    reason -- at the entry, by the declared window, and at the
    statement, by the conjunct [Equivalence.strong_equiv_va] puts in
    front of [strong_equiv] -- and not answered with the Sv48 limit;
    and (iii) that the unpinned predicate admits exactly what
    the three pinned ones admit, so the sealed family
    ([Equivalence.SPEC_VA_ANY] and its siblings) says what its name says.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.

(** ** (i) The Sv48 instance is today's constants

    [va_sp_window_lo] and [va_mmap_base_max] are DERIVED from the stack
    top by the formulas [State.sp_window_lo]'s and [State.mmap_base_max]'s
    notes give; these pins compare the derivation with the literal, so a
    slip in either direction shows up here rather than in a window that
    quietly moved.  The ones that hold by definition ([va_task_size Sv48]
    is [TASK_SIZE]) are documentary and say so. *)

Example sv48_task_size_is_TASK_SIZE : va_task_size Sv48 = TASK_SIZE.
Proof. reflexivity. Qed.  (* by definition *)

Example sv48_task_size_is_2_47 : va_task_size Sv48 = (2 ^ 47)%Z.
Proof. vm_compute. reflexivity. Qed.

Example sv48_stack_top_is_the_window_top : va_stack_top Sv48 = sp_window_hi.
Proof. reflexivity. Qed.  (* by definition *)

Example sv48_window_lo_is_the_literal : va_sp_window_lo Sv48 = sp_window_lo.
Proof. vm_compute. reflexivity. Qed.

Example sv48_window_hi_is_the_literal : va_sp_window_hi Sv48 = sp_window_hi.
Proof. vm_compute. reflexivity. Qed.

Example sv48_mmap_base_max_is_the_literal : va_mmap_base_max Sv48 = mmap_base_max.
Proof. vm_compute. reflexivity. Qed.

Example sv48_mmap_base_min_is_the_literal : va_mmap_base_min Sv48 = mmap_base_min.
Proof. reflexivity. Qed.  (* by definition *)

(** The predicates, not only the numbers: under an [Sv48] input,
    [Run.valid_entry] is the literal predicate conjunct for conjunct
    ([Run.valid_entry_sv48]), fired here at the fixture input so the
    lemma is seen to apply to the inputs the examples use.  The fifth
    conjunct is the launch one: the stack top, the sp window around it
    and the mmap base are what [Run.entry_launch_ok_va] pins, and the
    first four are read off it rather than standing beside it. *)
Example demo_entry_predicate_is_the_sv48_one : forall img en fs0 s,
  valid_entry img en (demo_input fs0 s)
  <-> match img, en with
      | mkImage segs _ _, mkEntry sp brk0 mbase _ =>
        valid_sp sp /\ valid_brk segs brk0 /\ valid_mmap_base mbase
        /\ entry_stack_fits sp (in_argv (demo_input fs0 s))
             (in_envp (demo_input fs0 s))
        /\ entry_launch_ok_va Sv48 en (demo_input fs0 s)
      end.
Proof. intros. apply valid_entry_sv48. reflexivity. Qed.

(** ** Sv57 shares the window and differs in the limit

    [MMAP_VA_BITS] saturates at 48 (arch/riscv/include/asm/pgtable.h,
    Linux v6.18.46, commit 1f99e9ab748f), so an Sv57 kernel places its
    stack and its mmap base where an Sv48 one does and differs only in
    [TASK_SIZE_64].  Both halves pinned, because a change that moved the
    window with the limit would be wrong in exactly the way this file
    exists to catch. *)
Example sv57_window_is_sv48s :
  va_sp_window_lo Sv57 = va_sp_window_lo Sv48
  /\ va_sp_window_hi Sv57 = va_sp_window_hi Sv48
  /\ va_mmap_base_min Sv57 = va_mmap_base_min Sv48
  /\ va_mmap_base_max Sv57 = va_mmap_base_max Sv48.
Proof. repeat split; reflexivity. Qed.

Example sv57_task_size_is_2_56 : va_task_size Sv57 = (2 ^ 56)%Z.
Proof. vm_compute. reflexivity. Qed.

Example sv57_limit_is_not_sv48s : va_task_size Sv57 <> va_task_size Sv48.
Proof. vm_compute. discriminate. Qed.

(** Under Sv39 the two coincide: [STACK_TOP = TASK_SIZE = 2^38]. *)
Example sv39_top_is_the_whole_space :
  va_task_size Sv39 = (2 ^ 38)%Z /\ va_stack_top Sv39 = (2 ^ 38)%Z.
Proof. split; vm_compute; reflexivity. Qed.

Example sv39_window :
  va_sp_window_lo Sv39 = 0x3f80000000%Z /\ va_sp_window_hi Sv39 = 0x4000000000%Z.
Proof. split; vm_compute; reflexivity. Qed.

(** ** (ii) A wrong declaration is red for the right reason

    AT THE ENTRY: the bottom of the Sv48 window is a placement every
    example uses, and the Sv39 window refuses it -- it lies 254 GiB
    above the last address an Sv39 process has -- while the Sv57 window
    admits it.  The refusal is by the window's upper bound, which is the
    reason the model would give ([Run.valid_sp_va]). *)
Definition sv48_window_bottom : word := Z_to_bv 64 sp_window_lo.

Example sv48_window_bottom_valid_under_sv48 : valid_sp_va Sv48 sv48_window_bottom.
Proof.
  unfold valid_sp_va, sv48_window_bottom, va_sp_window_lo, va_sp_window_hi,
    va_stack_top, sp_window_lo, sp_window_hi.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  lia.
Qed.

Example sv48_window_bottom_refused_under_sv39 : ~ valid_sp_va Sv39 sv48_window_bottom.
Proof.
  unfold valid_sp_va, sv48_window_bottom, va_sp_window_lo, va_sp_window_hi,
    va_stack_top, sv39_task_size, sp_window_lo.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  intros (_ & H & _). lia.
Qed.

Example sv48_window_bottom_valid_under_sv57 : valid_sp_va Sv57 sv48_window_bottom.
Proof.
  unfold valid_sp_va, sv48_window_bottom, va_sp_window_lo, va_sp_window_hi,
    va_stack_top, sp_window_lo, sp_window_hi.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  lia.
Qed.

(** AT AN ADDRESS: 2^40 is inside the Sv48 user space and past the whole
    of the Sv39 one.  Today's [State.access_okb] admits a range there --
    it compares against the Sv48 [TASK_SIZE] -- so an Sv39 run that
    reached it would be ANSWERED wrongly, which is why such a run is
    declined before it can ask.  This pair is the reason for the
    decline, stated as the two numbers. *)
Example an_sv48_address_beyond_sv39 :
  access_okb (Z_to_bv 64 (2 ^ 40)) 8 = true
  /\ (va_task_size Sv39 <? 2 ^ 40)%Z = true.
Proof. split; vm_compute; reflexivity. Qed.

(** AT THE STATEMENT: the fixture input under each declaration.  The
    three differ in the declaration alone. *)
Definition sized_input (v : VaSize) : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (Z_to_bv 64 0) demo_hwcap false v.

(** Under Sv39 or Sv57 the sealed predicate is refused whatever the
    images and entries -- its first conjunct is false -- and under Sv48
    it is [strong_equiv] itself, so nothing here touches what every other
    example proves.  [Run.run] is deliberately NOT consulted on the
    refused side: it is the Sv48 run whatever the input declares, which
    is a known limitation of the model, and these pins are about the
    statements that stand in front of it. *)
Example sv39_statement_refused : forall s t en_s en_t,
  ~ strong_equiv_va s t en_s en_t (sized_input Sv39).
Proof. intros s t en_s en_t (H & _). discriminate H. Qed.

Example sv57_statement_refused : forall s t en_s en_t,
  ~ strong_equiv_va s t en_s en_t (sized_input Sv57).
Proof. intros s t en_s en_t (H & _). discriminate H. Qed.

(** THE CONTROL for the two refusals above: with the same images, the
    same entries and the same input except for the declaration, the
    sealed predicate is not refused -- it IS the equivalence question,
    whatever its answer -- so what the refusals bite on is the
    declaration and nothing else about the triple.  Documentary in
    form: it is [Equivalence.strong_equiv_va_sv48] at the fixture input,
    and takes no entry or validity hypothesis because none is needed
    for the conclusion. *)
Example sv48_statement_is_strong_equiv : forall s t en_s en_t,
  strong_equiv_va s t en_s en_t (sized_input Sv48)
  <-> strong_equiv s t en_s en_t (sized_input Sv48).
Proof. intros. apply strong_equiv_va_sv48. reflexivity. Qed.

(** ** (iii) The unpinned predicate admits what each instance admits

    The three sized inputs are valid under [valid_input_va_any], each is
    valid under exactly its own pinned predicate, and the split lemma
    sends each to the right one.  The shared-clause proof is the one
    [Checks.Examples.demo_input_valid] uses, and it never mentions the
    declaration, which is the point: the size is the only clause the
    three predicates disagree on. *)
Lemma sized_input_va_any : forall v, valid_input_va_any (sized_input v).
Proof.
  intros v.
  unfold valid_input_va_any, valid_argv, valid_envp.
  cbn [mkProcInput in_argv in_envp in_fs].
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try (unfold valid_hwcap; left; reflexivity);
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | split
                 | cbn; lia | reflexivity | intros [] ].
  all: try valid_urandom_default.
  (* [Run.valid_launch]'s first half: a positional [mkProcInput] gets
     [State.default_execfn], the one-byte relative name "a".  That is a
     name [getname_flags] (fs/namei.c, Linux v6.18.46, commit
     1f99e9ab748f) can return -- one byte, no NUL -- so the first of
     [Run.valid_execfn]'s three arms applies. *)
  all: try (left; split;
            [ cbn; lia
            | cbn; intros [H | []];
              apply (proj2 (bv_eqb_eq _ _)) in H; vm_compute in H;
              discriminate ]).
  (* ...and its second half: this launch is a handful of bytes -- one
     empty argv string's NUL, the name and its NUL, and one pointer
     slot -- far under the E2BIG limit [bprm_stack_limits] (fs/exec.c)
     computes. *)
  all: try (vm_compute; discriminate).
Qed.

Example sized_sv48_valid : valid_input (sized_input Sv48).
Proof.
  destruct (sized_input_va_any Sv48) as (a & b & c & k & d & e & f & g & h & u & l).
  exact (conj a (conj b (conj c (conj k (conj d (conj e (conj f (conj g (conj h (conj eq_refl (conj u l))))))))))).
Qed.

Example sized_sv39_valid : valid_input_sv39 (sized_input Sv39).
Proof.
  destruct (sized_input_va_any Sv39) as (a & b & c & k & d & e & f & g & h & u & l).
  exact (conj a (conj b (conj c (conj k (conj d (conj e (conj f (conj g (conj h (conj eq_refl (conj u l))))))))))).
Qed.

Example sized_sv57_valid : valid_input_sv57 (sized_input Sv57).
Proof.
  destruct (sized_input_va_any Sv57) as (a & b & c & k & d & e & f & g & h & u & l).
  exact (conj a (conj b (conj c (conj k (conj d (conj e (conj f (conj g (conj h (conj eq_refl (conj u l))))))))))).
Qed.

Example each_instance_refuses_the_others :
  ~ valid_input (sized_input Sv39) /\ ~ valid_input (sized_input Sv57)
  /\ ~ valid_input_sv39 (sized_input Sv48) /\ ~ valid_input_sv39 (sized_input Sv57)
  /\ ~ valid_input_sv57 (sized_input Sv48) /\ ~ valid_input_sv57 (sized_input Sv39).
Proof.
  repeat split; intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _); discriminate H.
Qed.

Example va_any_splits_each_to_its_own :
  (valid_input (sized_input Sv48) \/ valid_input_sv39 (sized_input Sv48)
   \/ valid_input_sv57 (sized_input Sv48))
  /\ (valid_input (sized_input Sv39) \/ valid_input_sv39 (sized_input Sv39)
      \/ valid_input_sv57 (sized_input Sv39))
  /\ (valid_input (sized_input Sv57) \/ valid_input_sv39 (sized_input Sv57)
      \/ valid_input_sv57 (sized_input Sv57)).
Proof.
  repeat split; apply valid_input_va_any_splits; apply sized_input_va_any.
Qed.

(** ** The sealed statements, fired

    On the empty image -- which [Equivalence.image_brk_satisfiable]
    accepts, so its entry predicates are inhabited under every
    declaration -- the Sv39 and Sv57 statements are refuted, and so is
    the one that pins nothing, because it is their conjunction.  These
    are the refutations [Equivalence.strong_universal_T_sv39_refuted]
    states conditionally, with the condition discharged: a task sealed
    against [SPEC_SV39] today is refused by a theorem, not by a remark. *)
Definition empty_image : Image := mkImage [] 0%N demo_phdrs.

Example empty_image_brk_satisfiable :
  image_brk_satisfiable (img_segments empty_image) = true.
Proof. vm_compute. reflexivity. Qed.

Example sv39_statement_refuted_on_the_empty_image :
  ~ strong_universal_T_sv39 empty_image empty_image.
Proof.
  destruct (image_brk_satisfiable_entry_va empty_image (sized_input Sv39)
              (sized_input_va_any Sv39) empty_image_brk_satisfiable) as [en Hen].
  exact (strong_universal_T_sv39_refuted _ _ en en _ Hen Hen sized_sv39_valid).
Qed.

Example sv57_statement_refuted_on_the_empty_image :
  ~ strong_universal_T_sv57 empty_image empty_image.
Proof.
  destruct (image_brk_satisfiable_entry_va empty_image (sized_input Sv57)
              (sized_input_va_any Sv57) empty_image_brk_satisfiable) as [en Hen].
  exact (strong_universal_T_sv57_refuted _ _ en en _ Hen Hen sized_sv57_valid).
Qed.

(** The same image under the Sv48 input is a control: the refutation
    lemma cannot even be applied to it -- its declaration is not Sv39 --
    and the sealed predicate there is [strong_equiv], so whether the
    Sv48 statement holds of the empty image is the equivalence question
    and not the declaration. *)
Example empty_image_sv48_is_the_equivalence_question : forall en_s en_t,
  strong_equiv_va empty_image empty_image en_s en_t (sized_input Sv48)
  <-> strong_equiv empty_image empty_image en_s en_t (sized_input Sv48).
Proof. intros. apply strong_equiv_va_sv48. reflexivity. Qed.

Example va_any_statement_refuted_on_the_empty_image :
  ~ strong_universal_T_va_any empty_image empty_image.
Proof.
  intros H.
  apply strong_universal_T_va_any_splits in H.
  destruct H as (_ & H39 & _).
  exact (sv39_statement_refuted_on_the_empty_image H39).
Qed.
