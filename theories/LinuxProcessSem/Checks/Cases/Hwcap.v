(** * LinuxProcessSem.Checks.Cases.Hwcap — the declared AT_HWCAP word, word by word

    Mirrors the hardware-capability block of [Run.v] ([Run.valid_hwcap]
    and the declared predicates beside it) the way
    [Checks.Cases.VaSize] mirrors the address-space one.  The
    declaration is a value of the input, so what there is to pin is
    (i) that the DEFAULT is the two words and not one of them —
    [Run.valid_input_hwcap_splits] fired on the fixtures; (ii) that a
    wrong declaration is refused for the RIGHT reason, at the word and
    not at some other clause, and that both declarations refuse a word
    no kernel publishes; (iii) that the auxv entry the entry stack
    writes carries the DECLARED word under each declaration, so the
    declaration is about what the process can see; and (iv) the reason
    the declaration exists at all — that a V-extension PROBE leaves the
    modeled surface, so an advertised-V run of a binary carrying one is
    [MachineUnmodeled] even though the binary vectorises nothing.

    WHAT IS NOT HERE.  The sealed statement families
    ([Equivalence.SPEC_HWCAP_RV64GC] and the surfaces beside it) get no
    refutation, because unlike the per-size families there is nothing
    to refute: both words are words the spec arms carry, the statements
    stand behind the UNGATED [Equivalence.strong_equiv], and whether
    either holds of a given image pair is the equivalence question.  The
    split lemmas over the statements are proved where they are stated
    and need no fixture; (vi) below fires the ones for the three BUDGET
    cells, and pins the SHAPE of those lemmas
    where a later edit has to keep it -- which is all a firing without
    a fixture can do, and (vi) says so.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Instr DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.

(** ** The fixture

    The fixture input of [Checks.Cases.VaSize] with the AT_HWCAP word
    varied instead of the size: the declaration is the only field that
    moves, so everything below that bites, bites on it. *)
Definition hwcap_input (h : word) : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (Z_to_bv 64 0) h false Sv48.

(** The word the fixtures of this TREE launch with -- [Cases.Prelude]'s
    [demo_hwcap], not the [hwcap_input] above, which takes its word as a
    parameter and never mentions it -- said once here so the examples
    below can be read without opening that file: it is the mask WITHOUT
    V.  Documentary — it holds by definition. *)
Example the_trees_launch_word_is_the_v_less_mask : demo_hwcap = hwcap_rv64gc.
Proof. reflexivity. Qed.  (* by definition *)

(** ** (i) The default is the two, and each declaration holds of its own word

    Each pinned predicate is proved at its own word by the same
    shared-clause proof [Checks.Examples.demo_input_valid] uses, which
    never mentions the capability word; only the last conjunct differs,
    and it closes by [reflexivity] rather than by picking a side of a
    disjunction, which is the whole difference between a declaration and
    the default. *)
Example hwcap_input_gc_declared :
  valid_input_hwcap_rv64gc (hwcap_input hwcap_rv64gc).
Proof.
  unfold valid_input_hwcap_rv64gc, hwcap_input, valid_argv, valid_envp.
  cbn [in_argv in_envp in_fs].
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | split
                 | cbn; lia | reflexivity | intros [] ].
  all: try valid_urandom_default.
Qed.

Example hwcap_input_gcv_declared :
  valid_input_hwcap_rv64gcv (hwcap_input hwcap_rv64gcv).
Proof.
  unfold valid_input_hwcap_rv64gcv, hwcap_input, valid_argv, valid_envp.
  cbn [in_argv in_envp in_fs].
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | split
                 | cbn; lia | reflexivity | intros [] ].
  all: try valid_urandom_default.
Qed.

(** Both words are admitted by the DEFAULT, which is what makes a
    statement issued without a declaration a statement about both harts.
    Derived from the declared predicates rather than reproved, so the
    narrowing lemmas are exercised on a concrete input. *)
Example both_words_are_valid_under_the_default :
  valid_input (hwcap_input hwcap_rv64gc)
  /\ valid_input (hwcap_input hwcap_rv64gcv).
Proof.
  split.
  - exact (valid_input_of_valid_input_hwcap_rv64gc _ hwcap_input_gc_declared).
  - exact (valid_input_of_valid_input_hwcap_rv64gcv _ hwcap_input_gcv_declared).
Qed.

(** …and the split lemma sends each fixture to its OWN declaration, which
    is the exhaustiveness claim fired rather than stated: the default
    admits no third word, so a task held to [Run.valid_input] is held to
    exactly these two readings.

    STATED AS THE CONJUNCTION, not as a disjunction per fixture.  A disjunction
    would say only that SOME declaration catches each fixture, and a
    split lemma that always answered the left arm would satisfy it; the
    conclusion here names which arm, and the proof still runs through
    [Run.valid_input_hwcap_splits] rather than around it -- the wrong arm
    is closed by the word, on the spot. *)
Example the_default_splits_each_fixture_to_its_own :
  valid_input_hwcap_rv64gc (hwcap_input hwcap_rv64gc)
  /\ valid_input_hwcap_rv64gcv (hwcap_input hwcap_rv64gcv).
Proof.
  split.
  - destruct (valid_input_hwcap_splits _
                (valid_input_of_valid_input_hwcap_rv64gc _ hwcap_input_gc_declared))
      as [H | H]; [exact H |].
    exfalso. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & H & _ & _).
    apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate.
  - destruct (valid_input_hwcap_splits _
                (valid_input_of_valid_input_hwcap_rv64gcv _ hwcap_input_gcv_declared))
      as [H | H]; [| exact H].
    exfalso. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & H & _ & _).
    apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate.
Qed.

(** ** (ii) A wrong declaration is red, and for the word

    Each declaration refuses the OTHER word.  The refutation reads the
    capability conjunct and nothing else, and the control for it is
    [both_words_are_valid_under_the_default] above: the same fixture with
    the same every other field satisfies the default under both words, so
    what these refuse is the declaration. *)
Example each_declaration_refuses_the_other_word :
  ~ valid_input_hwcap_rv64gc (hwcap_input hwcap_rv64gcv)
  /\ ~ valid_input_hwcap_rv64gcv (hwcap_input hwcap_rv64gc).
Proof.
  split; intros (_ & _ & _ & _ & _ & _ & _ & _ & H & _ & _);
    apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate.
Qed.

(** …and BOTH refuse the words outside the pair, which is what keeps a
    declaration a declaration rather than a free parameter: the zero an
    absent AT_HWCAP entry effectively delivers, the A-less mask
    [0x112C], and [0x40112D], which sets a letter [riscv_fill_hwcap]
    never assigns.  The same words [Cases.Prelude]'s
    [valid_hwcap_refuses_the_absent_entrys_zero] and
    [valid_hwcap_refuses_masks_no_kernel_publishes] pin against the
    default, so the declarations refuse exactly where the default does
    and not more. *)
Example both_declarations_refuse_a_word_outside_the_pair :
  ~ valid_input_hwcap_rv64gc (hwcap_input (Z_to_bv 64 0))
  /\ ~ valid_input_hwcap_rv64gcv (hwcap_input (Z_to_bv 64 0))
  /\ ~ valid_input_hwcap_rv64gc (hwcap_input (Z_to_bv 64 0x112C))
  /\ ~ valid_input_hwcap_rv64gcv (hwcap_input (Z_to_bv 64 0x112C))
  /\ ~ valid_input_hwcap_rv64gc (hwcap_input (Z_to_bv 64 0x40112D))
  /\ ~ valid_input_hwcap_rv64gcv (hwcap_input (Z_to_bv 64 0x40112D)).
Proof.
  repeat split; intros (_ & _ & _ & _ & _ & _ & _ & _ & H & _ & _);
    apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate.
Qed.

(** THE DEFAULT refuses them too, on the same fixture, which is the
    control that the refusals above are not an artifact of the
    declarations being narrow: no launch carries these words at all. *)
Example the_default_refuses_a_word_outside_the_pair :
  ~ valid_input (hwcap_input (Z_to_bv 64 0))
  /\ ~ valid_input (hwcap_input (Z_to_bv 64 0x112C))
  /\ ~ valid_input (hwcap_input (Z_to_bv 64 0x40112D)).
Proof.
  repeat split; intros (_ & _ & _ & _ & _ & _ & _ & [H | H] & _ & _);
    apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate.
Qed.

(** ** (iii) The declared word is the word the process is handed

    A declaration that the auxv did not carry would be a claim about
    nothing.  [Cases.Prelude.auxv_hwcap_is_exactly_the_launch_word] says
    the AT_HWCAP entry carries the launch's word for every launch; under
    each declaration that word is the declared one, and this is that
    composition, stated once per declaration.  Quantified over every
    input the declaration accepts, so it is a claim about the
    declaration and not about the fixture.

    WHICH LEVEL THIS STOPS AT, so a reader does not over-read it: the
    claim is about [StackLayout.auxv_entries], the entry LIST, not about
    the bytes [StackLayout.build_stack_bytes] lays down.  The tie from
    the list to those bytes is [Cases.Prelude]'s
    [auxv_publishes_the_hart_capabilities], and it is made at the
    concrete [demo_hwcap] rather than for every word.  That is the
    strength [Cases.Prelude] already had; nothing here weakens it and
    nothing here extends it. *)
Example the_rv64gc_declaration_publishes_the_v_less_word :
  forall inp ph at_random,
    valid_input_hwcap_rv64gc inp ->
    filter (fun e => bv_eqb (fst e) AT_HWCAP)
           (auxv_entries ph at_random (in_uid inp) (in_hwcap inp))
    = [(AT_HWCAP, hwcap_rv64gc)].
Proof.
  intros inp ph at_random H.
  rewrite auxv_hwcap_is_exactly_the_launch_word.
  rewrite (valid_input_hwcap_rv64gc_word _ H). reflexivity.
Qed.

Example the_rv64gcv_declaration_publishes_the_v_word :
  forall inp ph at_random,
    valid_input_hwcap_rv64gcv inp ->
    filter (fun e => bv_eqb (fst e) AT_HWCAP)
           (auxv_entries ph at_random (in_uid inp) (in_hwcap inp))
    = [(AT_HWCAP, hwcap_rv64gcv)].
Proof.
  intros inp ph at_random H.
  rewrite auxv_hwcap_is_exactly_the_launch_word.
  rewrite (valid_input_hwcap_rv64gcv_word _ H). reflexivity.
Qed.

(** ** (iv) THE REASON THE DECLARATION EXISTS: the probe is unmodeled

    A runtime that wants to know whether it has a vector unit reads
    [vlenb], a V-extension CSR, and that read is `csrr t0, vlenb` --
    CSRRS with rd = t0, rs1 = x0 and csr = 0xC22, the word [0xC22022F3].

    IT IS NOT THE DECODER THAT DECLINES IT.  The word is a structurally
    ordinary Zicsr access and [DecodeC.decode_any] decodes it, which is
    worth pinning because the obvious guess -- that a V-extension probe
    is undecodable the way a vector instruction is -- is wrong, and a
    reader who assumed it would look for the decline in the wrong place.
    The decline is one level further in: [Sem.csr_slice] resolves only
    the fcsr aliases, so [Sem.exec_csr] answers [Sem.EIllegal],
    which [RiscvSemantics.interp_eff_accesses] reports as
    [MachineUnmodeled] -- the ISA semantics declining to say, not the
    architecture trapping.  Each level is pinned below, and then the
    composition of them.

    That is why the DECLARATION is the task's rather than the model's.
    Under the permissive default a statement about a binary carrying
    this probe ranges over [hwcap_rv64gcv] as well, the probe is taken,
    and the statement is false as issued even though the binary never
    vectorises anything.  Under [Run.valid_input_hwcap_rv64gc] the
    advertised word has no V bit, the probe is never reached, and the
    statement is the one such a task can prove.  Nothing here claims the
    hart lacks a vector unit; it claims the KERNEL published a word
    without the bit, which is a fact about the launch. *)
Example the_vlenb_probe_decodes_as_an_ordinary_csr_read :
  decode_any (Z_to_bv 32 0xC22022F3) = Some (Csr CSR_RS 5 0 3106, 4%Z).
Proof. check_eq. Qed.

Example the_model_resolves_no_vlenb_csr : csr_slice (Z_to_bv 12 0xC22) = None.
Proof. vm_compute. reflexivity. Qed.

Example the_vlenb_probe_leaves_the_modeled_surface : forall segs st,
  decode_exec_accesses segs st (Z_to_bv 32 0xC22022F3) = MachineUnmodeled.
Proof. intros segs st. reflexivity. Qed.

(** …and so does the vector work the probe would be guarding, by the
    OTHER route: a `vsetvli`, [0x0C0072D7], is a word the decoder does
    not decode at all.  Taken together the routes are what the declaration
    rests on -- that neither the probe nor the work it guards is modeled --
    rather than a claim about one encoding or one mechanism. *)
Example a_vector_word_is_not_decoded_at_all :
  decode_any (Z_to_bv 32 0x0C0072D7) = None.
Proof. vm_compute. reflexivity. Qed.

Example the_guarded_vector_word_leaves_the_modeled_surface : forall segs st,
  decode_exec_accesses segs st (Z_to_bv 32 0x0C0072D7) = MachineUnmodeled.
Proof. intros segs st. reflexivity. Qed.

(** THE CONTROL: the model is not answering [MachineUnmodeled] to
    everything.  A scalar word beside them -- `addi t0, zero, 0`,
    [0x00000293] -- is modeled, so what the declines above are about
    is the instruction and not the pin. *)
Example a_scalar_word_beside_them_is_modeled : forall segs st,
  decode_exec_accesses segs st (Z_to_bv 32 0x00000293) <> MachineUnmodeled.
Proof. intros segs st. cbn. discriminate. Qed.

(** ** (v) The abort stance carries the same declaration

    [Run.valid_input_abort_hwcap_rv64gc] and its twin are the cell for
    a binary that probes for a vector unit AND wants the abort path
    modeled.  The fixture is the one above with the
    declaration flipped, so the only field that differs from the
    default-stance fixtures is [State.in_abort_terminal] and the pins
    below bite on the capability word exactly as the ones above do. *)
Definition hwcap_abort_input (h : word) : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (Z_to_bv 64 0) h true Sv48.

Example hwcap_abort_input_gc_declared :
  valid_input_abort_hwcap_rv64gc (hwcap_abort_input hwcap_rv64gc).
Proof.
  unfold valid_input_abort_hwcap_rv64gc, hwcap_abort_input, valid_argv, valid_envp.
  cbn [in_argv in_envp in_fs].
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | split
                 | cbn; lia | reflexivity | intros [] ].
  all: try valid_urandom_default.
Qed.

Example hwcap_abort_input_gcv_declared :
  valid_input_abort_hwcap_rv64gcv (hwcap_abort_input hwcap_rv64gcv).
Proof.
  unfold valid_input_abort_hwcap_rv64gcv, hwcap_abort_input, valid_argv, valid_envp.
  cbn [in_argv in_envp in_fs].
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | split
                 | cbn; lia | reflexivity | intros [] ].
  all: try valid_urandom_default.
Qed.

(** The abort-stance split lemma, fired, and naming which arm catches
    each fixture for the reason the default-stance one does: the abort
    default admits the two words and no third, so a task that declares
    the stance and not the word is held to both readings of the hart. *)
Example the_abort_default_splits_each_fixture_to_its_own :
  valid_input_abort_hwcap_rv64gc (hwcap_abort_input hwcap_rv64gc)
  /\ valid_input_abort_hwcap_rv64gcv (hwcap_abort_input hwcap_rv64gcv).
Proof.
  split.
  - destruct (valid_input_abort_hwcap_splits _
                (valid_input_abort_of_valid_input_abort_hwcap_rv64gc
                   _ hwcap_abort_input_gc_declared)) as [H | H]; [exact H |].
    exfalso. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & H & _ & _).
    apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate.
  - destruct (valid_input_abort_hwcap_splits _
                (valid_input_abort_of_valid_input_abort_hwcap_rv64gcv
                   _ hwcap_abort_input_gcv_declared)) as [H | H]; [| exact H].
    exfalso. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & H & _ & _).
    apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate.
Qed.

Example each_abort_declaration_refuses_the_other_word :
  ~ valid_input_abort_hwcap_rv64gc (hwcap_abort_input hwcap_rv64gcv)
  /\ ~ valid_input_abort_hwcap_rv64gcv (hwcap_abort_input hwcap_rv64gc).
Proof.
  split; intros (_ & _ & _ & _ & _ & _ & _ & _ & H & _ & _);
    apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate.
Qed.

(** THE AXES ARE INDEPENDENT, and this is the pin that says so: the
    declaration of the word does not carry the declaration of the
    stance, in either direction.  Without it the declared predicates
    could have collapsed onto each other without any example noticing. *)
Example the_word_declaration_does_not_carry_the_stance :
  ~ valid_input_hwcap_rv64gc (hwcap_abort_input hwcap_rv64gc)
  /\ ~ valid_input_abort_hwcap_rv64gc (hwcap_input hwcap_rv64gc).
Proof.
  split; intros (_ & _ & _ & _ & _ & _ & _ & _ & H & _); discriminate H.
Qed.

(** ** (vi) The budget cells' split lemmas, their shape pinned

    The statement-level splits for the three budget cells
    -- the unconfigured budget shells under each stance, and the
    configured one with the stance off -- fired once each, plain and
    error-free.  Their splits are held to a shape here and not only
    where they are stated.

    WHAT THESE PIN, AND WHAT THEY DO NOT.  As a proposition each one is
    its split lemma with the [<->] unfolded and the backward half
    uncurried, so it establishes NO NEW FACT, and no instantiation of
    it could go red: it quantifies over all image pairs, including the
    pairs where every statement it names is false.  That makes these
    WEAKER than the fixture firings above, which run a concrete input
    through a split and can fail on the input.  What they pin is the
    SHAPE of the split lemma, at a site a later edit has to keep
    compiling:

    - both declared statements are named independently in the example's
      own type, so a split lemma whose two arms collapsed onto one
      statement stops typechecking here -- [proj1] would carry
      [A -> B /\ B] into a goal of [A -> B /\ C];
    - both directions of the [<->] are named, so dropping a half breaks
      it;
    - renaming or deleting a split lemma breaks it, which is the one of
      the three a bare [Check] would also catch.

    WHAT A BITING PIN WOULD BE, AND WHY IT IS NOT HERE.  An
    instantiation at an image pair for which the undeclared statement
    is PROVED, so the forward half hands back two declared statements
    about a real binary.  [Checks/Omni.v] proves the constant-pinned
    and configured statements for [exit0_image], and the
    budget-abstracted ones are reachable from those through
    [Equivalence.strong_universal_T_budgets_of_pinned] -- but that
    firing has to live downstream of [Checks/Omni.v], and [Omni]
    imports [Checks.Examples], which re-exports this file.  This
    section cannot reach it. *)
Example the_budgets_cell_is_exactly_its_two_declarations :
  forall (ls lt : Z) (s t : Image),
    (strong_universal_T_budgets ls lt s t
     -> strong_universal_T_budgets_hwcap_rv64gc ls lt s t
        /\ strong_universal_T_budgets_hwcap_rv64gcv ls lt s t)
    /\ (strong_universal_T_budgets_hwcap_rv64gc ls lt s t
        -> strong_universal_T_budgets_hwcap_rv64gcv ls lt s t
        -> strong_universal_T_budgets ls lt s t).
Proof.
  intros ls lt s t. split.
  - exact (proj1 (strong_universal_T_budgets_hwcap_splits ls lt s t)).
  - intros Hgc Hgcv.
    exact (proj2 (strong_universal_T_budgets_hwcap_splits ls lt s t)
                 (conj Hgc Hgcv)).
Qed.

Example the_error_free_budgets_cell_is_exactly_its_two_declarations :
  forall (ls lt : Z) (s t : Image),
    (strong_universal_error_free_T_budgets ls lt s t
     -> strong_universal_error_free_T_budgets_hwcap_rv64gc ls lt s t
        /\ strong_universal_error_free_T_budgets_hwcap_rv64gcv ls lt s t)
    /\ (strong_universal_error_free_T_budgets_hwcap_rv64gc ls lt s t
        -> strong_universal_error_free_T_budgets_hwcap_rv64gcv ls lt s t
        -> strong_universal_error_free_T_budgets ls lt s t).
Proof.
  intros ls lt s t. split.
  - exact (proj1 (strong_universal_error_free_T_budgets_hwcap_splits ls lt s t)).
  - intros Hgc Hgcv.
    exact (proj2 (strong_universal_error_free_T_budgets_hwcap_splits ls lt s t)
                 (conj Hgc Hgcv)).
Qed.

Example the_abort_budgets_cell_is_exactly_its_two_declarations :
  forall (ls lt : Z) (s t : Image),
    (strong_universal_T_budgets_abort ls lt s t
     -> strong_universal_T_budgets_abort_hwcap_rv64gc ls lt s t
        /\ strong_universal_T_budgets_abort_hwcap_rv64gcv ls lt s t)
    /\ (strong_universal_T_budgets_abort_hwcap_rv64gc ls lt s t
        -> strong_universal_T_budgets_abort_hwcap_rv64gcv ls lt s t
        -> strong_universal_T_budgets_abort ls lt s t).
Proof.
  intros ls lt s t. split.
  - exact (proj1 (strong_universal_T_budgets_abort_hwcap_splits ls lt s t)).
  - intros Hgc Hgcv.
    exact (proj2 (strong_universal_T_budgets_abort_hwcap_splits ls lt s t)
                 (conj Hgc Hgcv)).
Qed.

Example the_error_free_abort_budgets_cell_is_exactly_its_two_declarations :
  forall (ls lt : Z) (s t : Image),
    (strong_universal_error_free_T_budgets_abort ls lt s t
     -> strong_universal_error_free_T_budgets_abort_hwcap_rv64gc ls lt s t
        /\ strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv ls lt s t)
    /\ (strong_universal_error_free_T_budgets_abort_hwcap_rv64gc ls lt s t
        -> strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv ls lt s t
        -> strong_universal_error_free_T_budgets_abort ls lt s t).
Proof.
  intros ls lt s t. split.
  - exact (proj1 (strong_universal_error_free_T_budgets_abort_hwcap_splits ls lt s t)).
  - intros Hgc Hgcv.
    exact (proj2 (strong_universal_error_free_T_budgets_abort_hwcap_splits ls lt s t)
                 (conj Hgc Hgcv)).
Qed.

Example the_scfg_budgets_cell_is_exactly_its_two_declarations :
  forall (cfg : SpuriousCfg) (ls lt : Z) (s t : Image),
    (strong_universal_T_scfg_budgets cfg ls lt s t
     -> strong_universal_T_scfg_budgets_hwcap_rv64gc cfg ls lt s t
        /\ strong_universal_T_scfg_budgets_hwcap_rv64gcv cfg ls lt s t)
    /\ (strong_universal_T_scfg_budgets_hwcap_rv64gc cfg ls lt s t
        -> strong_universal_T_scfg_budgets_hwcap_rv64gcv cfg ls lt s t
        -> strong_universal_T_scfg_budgets cfg ls lt s t).
Proof.
  intros cfg ls lt s t. split.
  - exact (proj1 (strong_universal_T_scfg_budgets_hwcap_splits cfg ls lt s t)).
  - intros Hgc Hgcv.
    exact (proj2 (strong_universal_T_scfg_budgets_hwcap_splits cfg ls lt s t)
                 (conj Hgc Hgcv)).
Qed.

Example the_error_free_scfg_budgets_cell_is_exactly_its_two_declarations :
  forall (cfg : SpuriousCfg) (ls lt : Z) (s t : Image),
    (strong_universal_error_free_T_scfg_budgets cfg ls lt s t
     -> strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc cfg ls lt s t
        /\ strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv cfg ls lt s t)
    /\ (strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc cfg ls lt s t
        -> strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv cfg ls lt s t
        -> strong_universal_error_free_T_scfg_budgets cfg ls lt s t).
Proof.
  intros cfg ls lt s t. split.
  - exact (proj1 (strong_universal_error_free_T_scfg_budgets_hwcap_splits cfg ls lt s t)).
  - intros Hgc Hgcv.
    exact (proj2 (strong_universal_error_free_T_scfg_budgets_hwcap_splits cfg ls lt s t)
                 (conj Hgc Hgcv)).
Qed.

Print Assumptions the_rv64gc_declaration_publishes_the_v_less_word.
Print Assumptions the_default_splits_each_fixture_to_its_own.
Print Assumptions the_vlenb_probe_leaves_the_modeled_surface.
Print Assumptions the_abort_default_splits_each_fixture_to_its_own.
Print Assumptions the_budgets_cell_is_exactly_its_two_declarations.
Print Assumptions the_scfg_budgets_cell_is_exactly_its_two_declarations.
