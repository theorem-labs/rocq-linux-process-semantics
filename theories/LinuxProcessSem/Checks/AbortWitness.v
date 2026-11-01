(** * LinuxProcessSem.Checks.AbortWitness — an image that really aborts

    Not part of the trusted specification: this file is QA on the
    definitions, in the sense [Checks/Examples.v] describes, and it
    exists to close one specific gap in that file's abort-family
    statements.

    ** The gap

    [Equivalence.error_free_unkilled] is [Equivalence.error_free] plus
    "and it is not killed", and the abort-declared statement family is
    stated with it.  Two things suggest that the extra
    conjunct is doing work, and both stop short of a run:

    - [Equivalence.error_free_unkilled_bites] exhibits a [behavior] whose
      trace set contains a [State.KillEv].  That behavior is HAND-WRITTEN.
      It shows the two PREDICATES differ on something of the right type;
      it does not show that any IMAGE separates them, and a [Run.behavior]
      is a record of bare [Prop]s, so nothing stops one being written
      that no [Run.run] returns.
    - [Equivalence.strong_universal_error_free_T_abort_refuted_by_abort]
      takes [Equivalence.dies_by_signal (Run.run …)] as a HYPOTHESIS.
      Without an image that discharges it, the abort family's
      refutation is stated conditionally and never fires.  A conditional refutation whose condition is never met is
      indistinguishable, from inside the development, from one whose
      condition is unsatisfiable.

    This file supplies the missing half: a concrete six-instruction image
    whose run reaches [State.KillEv], and the two statements that fall
    out of it — [abrt_dies_by_signal], which discharges the hypothesis,
    and [abrt_refutes_error_free_abort], which is the refutation actually
    fired at a real image.  It is the abort-declared twin of
    [Checks.Examples.undecodable_image_refutes_error_free_equivalence],
    and it is deliberately built the way that one is: at a valid entry,
    on a valid input, so that a statement quantified over those is really
    reached.

    A second image, [abrt_blocked], closes a second gap: the launch whose
    signal mask already blocks SIGABRT.  [Run.valid_sigmask] allows that
    launch, and on it musl's [raise(SIGABRT)] returns, so [abort] goes on
    to its second path.  [abrt_blocked_dies_by_signal] and
    [abrt_blocked_error_free] say that the model follows that path to the
    death and that no execution of it reaches [Run.SError].  The last
    part of this file says why each half needs the other.

    ** Why an image is needed rather than a longer argument

    [Equivalence.dies_by_signal] is read off [Run.behavior]'s trace set,
    and [Run.run]'s trace set is [Run.obs_trace] of the initial
    configuration — an existential over [Run.star].  So the only way to
    satisfy it is to walk a real execution, and walking one is what
    catches the things prose does not: that the tid the [tkill] names has
    to be the one the model CHOSE rather than a constant the image
    carries, that the choice is made by a syscall the program has to
    issue first, and that [Run.sstep_killed] rather than [Run.sstep_exit]
    is the rule that fires at the end.

    ** The program

    Six instructions at 0x100, the shortest that can abort under this
    model, written as the hex a loader would have produced:

    #<pre>
      addi a7, x0, 96     06000893   set_tid_address
      addi a0, x0, 0      00000513   tidptr = NULL
      ecall               00000073   -> a0 = the tid the model chose
      addi a7, x0, 130    08200893   tkill
      addi a1, x0, 6      00600593   SIGABRT
      ecall               00000073   -> killed
    #</pre>

    THE FIRST SYSCALL IS NOT CEREMONY.  [Kernel.Signal.tkill_self]
    declines with [Monad.unmodeled] while [State.m_tid] is [None], and
    declines again unless the [pid] it is handed EQUALS the recorded tid.
    [Kernel.Fork.set_tid_address_spec] is what pins it, and it pins it to
    a value drawn with [Monad.choose] from the whole
    [Kernel.Fork.PID_MAX_ENVELOPE] window — the model cannot predict it,
    exactly as it cannot predict getrandom's bytes.  So no image can
    carry the right [pid] as an immediate.  What makes this program work
    is that [Run.apply_effect] writes the syscall's return value into a0
    and neither instruction between the two [ecall]s touches a0, so the
    tid flows from the kernel's answer straight into [tkill]'s first
    argument.  That is musl's own arrangement read back one level:
    [__init_tp] seeds [__pthread_self()->tid] from [set_tid_address], and
    [raise] sends to it.

    The choice is why this file's [abrt_eff1] names 4242: any value in
    the window would do, this is one, and it is
    [Cases.Kernel.Signal.abort_tid] so that the fixture and the run agree.

    THE MASK IS THE OTHER PREMISE.  [abrt_input] launches with
    [State.in_sigmask] clear, so SIGABRT is not blocked and
    [Kernel.Signal.send_sigabrt] takes the [State.with_killed] branch
    rather than the [State.with_sigabrt_pending] one.  musl's real
    [raise] blocks first and dies on the mask restore two calls later;
    that longer path is deliberately NOT what this first image walks —
    the shortest path to a [State.KillEv] is what a non-vacuity witness
    wants.  The longest path, the one a launch that blocks SIGABRT takes,
    is the second image's.

    ADMISSION REASON (the third at the top of [Checks/Examples.v]): what
    is pinned here is that a [Run.run]'s TRACE SET contains a
    [State.KillEv], which is a statement about the model's own execution
    relation, not about anything a real run reveals. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs Examples Omni.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The image, the launch, and the two syscall answers
   ========================================================================= *)

Definition abrt_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 24;
  seg_perms := "r-x"%string;
  seg_bytes := ["930800061305000073000000930820089305600073000000"%pstring];
  seg_kind  := SegLoader
|}.
Definition abrt_segments : list Segment := [abrt_segment].
Definition abrt_image : Image := mkImage abrt_segments 0x100 demo_phdrs.

(** The same launch [Checks.Examples] runs its images on — one empty
    argument, no environment, an empty file system, end of input — with
    the two fields this file needs pinned: [State.in_sigmask] clear, so
    SIGABRT is deliverable, and [State.in_abort_terminal] SET, which is
    what [Run.valid_input_abort] asks for and what
    [Kernel.Signal.tkill_spec] tests first. *)
Definition abrt_input : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) demo_hwcap true Sv48.

Example abrt_input_declares_abort : in_abort_terminal abrt_input = true.
Proof. reflexivity. Qed.

(** [Run.valid_input_abort], proved the way
    [Checks.Examples.demo_input_valid] proves [Run.valid_input] — the same
    shared clauses, the same guarded arms, and the abort declaration this
    file is about rather than its negation. *)
Example abrt_input_valid : valid_input_abort abrt_input.
Proof.
  unfold valid_input_abort, abrt_input, valid_argv, valid_envp.
  cbn [mkProcInput in_argv in_envp in_fs in_execfn].
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try (unfold valid_hwcap; left; reflexivity);
    (* [Fs.fs_image_real], the FIFTH conjunct: the image is the empty
       one, with no key to be non-canonical and no key under another,
       so the boolean computes to [true]. *)
    try (unfold fs_image_real; vm_compute; reflexivity);
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | split
                 | cbn; lia | reflexivity | intros [] ].
  all: try valid_urandom_default.
  (* [Run.valid_launch]'s first half: the launch name is
     [State.default_execfn], "a" -- one byte, no NUL -- so it is a name
     [getname_flags] (fs/namei.c, Linux v6.18.46, commit 1f99e9ab748f)
     can return, and the first of [Run.valid_execfn]'s three arms
     applies. *)
  all: try (unfold valid_execfn, default_execfn, valid_path_name;
            left; split;
            [ cbn [length]; lia
            | cbn [In]; intros [H | []];
              apply (proj2 (bv_eqb_eq _ _)) in H; vm_compute in H;
              discriminate ]).
  (* ... and its second half: this launch is eleven bytes -- the empty
     argument's NUL, the name and its NUL, and one pointer slot --
     against the E2BIG limit [bprm_stack_limits] (fs/exec.c) computes. *)
  all: try (unfold launch_bytes, e2big_limit, default_execfn;
            cbn [in_argv in_envp in_execfn]; vm_compute; discriminate).
Qed.

(** The entry is the one [Checks.Examples.demo_entry_of] gives this
    launch: [Run.launch_entry_va], the placement [execve] itself would
    compute from the input.  [Run.launch_entry_va_valid] proves every
    conjunct of [Run.valid_entry] but [Run.valid_brk] from the launch
    alone, and [Run.valid_brk] is the only one this image can change:
    its single segment sits in the first page, so the break base
    [Checks.Examples] uses serves here too.

    THE ENTRY IS A FUNCTION OF THE INPUT rather than a constant, which
    is what the fifth conjunct of [Run.valid_entry_va]
    ([Run.entry_launch_ok_va]) forces: the entry stack pointer has to
    lie in the window [create_elf_tables] (fs/binfmt_elf.c, Linux
    v6.18.46, commit 1f99e9ab748f) leaves for THAT launch's strings and
    auxiliary vector, so no one address serves every input.  The
    quantifier over inputs survives unchanged; only the entry moves
    with them.  Taking the address size from [State.in_va_size] inside
    [Checks.Examples.demo_entry_of] is what makes the conclusion
    [Run.valid_entry] with no rewrite. *)
Example demo_entry_valid_abrt : forall inp,
  valid_input_abort inp -> valid_entry abrt_image (demo_entry_of inp) inp.
Proof.
  intros inp Hvalid.
  (* Guarded rather than positional: [Run.valid_input_abort] grows a
     conjunct whenever the input class learns to say something new, and
     the three clauses this proof needs -- [Run.valid_argv],
     [Run.valid_envp] and [Run.valid_launch] -- are then found by
     [assumption] rather than by counting.  [match goal] is syntactic,
     so [red] is what makes it fire, and [valid_launch] stays folded
     under it and arrives whole. *)
  red in Hvalid.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  unfold valid_entry, demo_entry_of, abrt_image.
  apply launch_entry_va_valid; try assumption.
  unfold valid_brk.
  repeat split; vm_compute; try reflexivity; try discriminate.
Qed.

(** The entry this file's RUNS are stepped at: the entry of the input
    they are run on.  [Checks.Examples.demo_entry] is the entry of that
    file's own launch, and two launches whose argument vectors differ
    get different stack pointers, so a fixture names its own. *)
Definition abrt_entry : ExecEntry := demo_entry_of abrt_input.

Lemma abrt_entry_valid : valid_entry abrt_image abrt_entry abrt_input.
Proof. exact (demo_entry_valid_abrt _ abrt_input_valid). Qed.

(* =========================================================================
   Walking the run
   ========================================================================= *)

(** THE PLACEMENT IS [abrt_entry]'S, READ OFF IT rather than repeated
    as literals: the entry's four fields are what [Run.init_config]
    passes, so the run stated at [abrt_entry] and the states walked
    below agree whatever placement [Checks.Examples.demo_entry_of]
    computes for this launch.  [Run.init_machine_state] lays the entry
    block from [abrt_sp] up to the stack VMA's end
    [StackLayout.ed_top] of [abrt_draw], so the two have to come from
    the same entry. *)
Definition abrt_sp : word := en_sp abrt_entry.
Definition abrt_brk : word := en_brk abrt_entry.
Definition abrt_mbase : word := en_mmap_base abrt_entry.
Definition abrt_draw : EntryDraw := en_draw abrt_entry.

Lemma abrt_entry_fields :
  abrt_entry = mkEntry abrt_sp abrt_brk abrt_mbase abrt_draw.
Proof.
  unfold abrt_sp, abrt_brk, abrt_mbase, abrt_draw. destruct abrt_entry.
  reflexivity.
Qed.

(** The states along the first leg, named by their step count, with the
    memory abstracted exactly as [Checks.Omni]'s [wloop_msk] family
    abstracts it: no instruction of this image writes memory, so every
    state on the way carries the initial one's. *)
Definition abrt_ms0 : machine_state :=
  init_machine_state abrt_segments 0x100 demo_phdrs abrt_sp abrt_mbase
    abrt_draw abrt_input.
Definition abrt_msk (k : nat) : machine_state :=
  match run_steps k abrt_segments abrt_ms0 with
  | Some ms => ms
  | None => abrt_ms0
  end.
Definition abrt_s (k : nat) : machine_state :=
  with_mem (abrt_msk k) (ms_mem abrt_ms0).

Definition abrt_model (lim : Z) : Model :=
  init_model (segments_reserved abrt_segments) abrt_brk abrt_mbase abrt_sp
    lim abrt_input.
Definition abrt_c (lim : Z) : config := mkCfg (abrt_s 0) (abrt_model lim).

Lemma abrt_config : forall lim,
  init_config abrt_segments 0x100 demo_phdrs abrt_sp abrt_brk abrt_mbase
    abrt_draw lim abrt_input
  = abrt_c lim.
Proof.
  intros lim. unfold init_config, abrt_c.
  f_equal; try exact (with_mem_eta abrt_ms0).
Qed.

Lemma abrt_step : forall k, (k < 3)%nat -> forall mem,
  RiscvSemantics.step abrt_segments (with_mem (abrt_msk k) mem)
  = MachineOk (with_mem (abrt_msk (S k)) mem).
Proof.
  intros k Hk mem.
  do 3 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
Qed.

Lemma abrt_instr_sstep : forall lim k, (k < 3)%nat ->
  sstep abrt_segments (mkCfg (abrt_s k) (abrt_model lim)) []
    (SNext (mkCfg (abrt_s (S k)) (abrt_model lim))).
Proof.
  intros lim k Hk. unfold abrt_s.
  apply sstep_instr; [reflexivity | |].
  - do 3 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
  - no_lazy. rewrite (abrt_step k Hk). reflexivity.
Qed.

(** Three instructions in -- the two [addi]s and the [ecall] itself, which
    is an ordinary instruction step that leaves the number pending -- the
    first syscall is at the door and its number is 96. *)
Lemma abrt_svc3 : ms_svc_pending (abrt_s 3) = Some (Z_to_bv 64 96).
Proof. vm_compute. first [reflexivity | f_equal; apply bv_eq; reflexivity]. Qed.

(** THE TID THE MODEL CHOOSES.  [Monad.choose] admits any value in the
    window, so this effect names one; [abrt_sc1] is the statement that
    the acceptor agrees it is admissible, and nothing below depends on
    which one it is. *)
Definition abrt_eff1 : SyscallEffect := mkEffect abort_tid [] [].

Lemma abrt_sc1 : forall lim,
  check_syscall (sys_input abrt_segments (abrt_s 3) (Z_to_bv 64 96)) abrt_eff1
    (abrt_model lim)
  = CheckOk (with_tid abort_tid (abrt_model lim)) [].
Proof. intros lim. vm_compute. reflexivity. Qed.

(** The state the first syscall leaves: a0 holds the tid, and the pc has
    moved past the [ecall].  This is where the second leg starts. *)
Definition abrt_t0 : machine_state :=
  advance_past_svc (apply_effect (abrt_s 3) abrt_eff1).
Definition abrt_tk (k : nat) : machine_state :=
  match run_steps k abrt_segments abrt_t0 with
  | Some ms => ms
  | None => abrt_t0
  end.
(** The second leg abstracts ITS OWN memory rather than [abrt_ms0]'s.
    The two are equal — [abrt_eff1] carries no writes, copies, zeros or
    unmaps, and [Run.apply_effect] touches memory only through those —
    but naming [abrt_t0]'s is what lets [abrt_t 0] be [abrt_t0] by
    [Checks.Omni.with_mem_eta] alone, with no rewriting under
    [State.with_mem]. *)
Definition abrt_t (k : nat) : machine_state :=
  with_mem (abrt_tk k) (ms_mem abrt_t0).

Lemma abrt_syscall1_sstep : forall lim,
  sstep abrt_segments (mkCfg (abrt_s 3) (abrt_model lim)) []
    (SNext (mkCfg (abrt_t 0) (with_tid abort_tid (abrt_model lim)))).
Proof.
  intros lim.
  replace (abrt_t 0) with (advance_past_svc (apply_effect (abrt_s 3) abrt_eff1))
    by (unfold abrt_t, abrt_tk, run_steps; fold abrt_t0;
        exact (eq_sym (with_mem_eta abrt_t0))).
  eapply sstep_syscall;
    [ reflexivity
    | exact abrt_svc3
    | apply check_syscall_ok_iff; exact (abrt_sc1 lim)
    | reflexivity
    | apply materialize_model_accesses_no_lazy; reflexivity ].
Qed.

Lemma abrt_step2 : forall k, (k < 3)%nat -> forall mem,
  RiscvSemantics.step abrt_segments (with_mem (abrt_tk k) mem)
  = MachineOk (with_mem (abrt_tk (S k)) mem).
Proof.
  intros k Hk mem.
  do 3 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
Qed.

Lemma abrt_instr2_sstep : forall lim k, (k < 3)%nat ->
  sstep abrt_segments
    (mkCfg (abrt_t k) (with_tid abort_tid (abrt_model lim))) []
    (SNext (mkCfg (abrt_t (S k)) (with_tid abort_tid (abrt_model lim)))).
Proof.
  intros lim k Hk. unfold abrt_t.
  apply sstep_instr; [reflexivity | |].
  - do 3 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
  - no_lazy. rewrite (abrt_step2 k Hk). reflexivity.
Qed.

(** Three more instructions, and the second [ecall] is pending at 130. *)
Lemma abrt_svc_tkill : ms_svc_pending (abrt_t 3) = Some (Z_to_bv 64 130).
Proof. vm_compute. first [reflexivity | f_equal; apply bv_eq; reflexivity]. Qed.

(** The kill itself.  a0 carries the tid the first syscall returned, a1
    carries 6, and the post-model is [State.with_killed] — the same
    answer [Cases.Kernel.Signal.tkill_sigabrt_unblocked_kills] pins at a
    hand-built model, here reached from a real machine state whose
    registers the program put there. *)
Definition abrt_killed_model (lim : Z) : Model :=
  with_killed (Z_to_bv 64 6) (with_tid abort_tid (abrt_model lim)).

Lemma abrt_sc2 : forall lim,
  check_syscall (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130))
    (mkEffect (Z_to_bv 64 0) [] []) (with_tid abort_tid (abrt_model lim))
  = CheckOk (abrt_killed_model lim) [].
Proof. intros lim. vm_compute. reflexivity. Qed.

(** The trace the run ends on. *)
Definition abrt_trace (lim : Z) : list event :=
  [KillEv (Z_to_bv 64 6) (m_fs (abrt_killed_model lim))].

Lemma abrt_kill_sstep : forall lim,
  sstep abrt_segments
    (mkCfg (abrt_t 3) (with_tid abort_tid (abrt_model lim)))
    (abrt_trace lim)
    (SNext (mkCfg (abrt_t 3) (abrt_killed_model lim))).
Proof.
  intros lim. unfold abrt_trace.
  change [KillEv (Z_to_bv 64 6) (m_fs (abrt_killed_model lim))]
    with ([] ++ [KillEv (Z_to_bv 64 6) (m_fs (abrt_killed_model lim))]).
  eapply sstep_killed;
    [ reflexivity
    | exact abrt_svc_tkill
    | apply check_syscall_ok_iff; exact (abrt_sc2 lim)
    | reflexivity ].
Qed.

(** The whole execution: two instructions, [set_tid_address], two more
    instructions, [tkill], and the process is dead. *)
Lemma abrt_star : forall lim,
  star abrt_segments (abrt_c lim) (abrt_trace lim)
    (mkCfg (abrt_t 3) (abrt_killed_model lim)).
Proof.
  intros lim.
  change (abrt_trace lim)
    with ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++
         (abrt_trace lim ++ [])))))))).
  unfold abrt_c.
  eapply star_step; [exact (abrt_instr_sstep lim 0 ltac:(lia)) |].
  eapply star_step; [exact (abrt_instr_sstep lim 1 ltac:(lia)) |].
  eapply star_step; [exact (abrt_instr_sstep lim 2 ltac:(lia)) |].
  eapply star_step; [exact (abrt_syscall1_sstep lim) |].
  eapply star_step; [exact (abrt_instr2_sstep lim 0 ltac:(lia)) |].
  eapply star_step; [exact (abrt_instr2_sstep lim 1 ltac:(lia)) |].
  eapply star_step; [exact (abrt_instr2_sstep lim 2 ltac:(lia)) |].
  eapply star_step; [exact (abrt_kill_sstep lim) |].
  apply star_refl.
Qed.

(* =========================================================================
   What it buys
   ========================================================================= *)

(** THE HYPOTHESIS, DISCHARGED.  This is the statement
    [Equivalence.strong_universal_error_free_T_abort_refuted_by_abort]
    takes as an assumption. *)
Theorem abrt_dies_by_signal : forall lim,
  dies_by_signal (run abrt_image lim abrt_entry abrt_input).
Proof.
  intros lim.
  rewrite abrt_entry_fields. cbn [run bh_traces abrt_image].
  rewrite abrt_config.
  exists (abrt_trace lim), (Z_to_bv 64 6), (m_fs (abrt_killed_model lim)).
  split.
  - exists (abrt_trace lim), (mkCfg (abrt_t 3) (abrt_killed_model lim)).
    split; [exact (abrt_star lim) | apply is_prefix_refl].
  - now left.
Qed.

(** ... and therefore the abort family's bite is FIRED rather than
    stated.  [Equivalence.error_free_unkilled]'s second conjunct is what
    fails here: this run reaches no [Run.sstep] error at all — the model
    follows it to the end — so [Equivalence.error_free] alone would be
    SATISFIED by it, which is exactly the weakening
    [Equivalence.error_free_unkilled] exists to prevent.  A reader who
    wants the difference in one line has it here: the same run, accepted
    by one predicate and refused by the other. *)
Theorem abrt_refutes_error_free_abort :
  ~ strong_universal_error_free_T_abort abrt_image abrt_image.
Proof.
  apply (strong_universal_error_free_T_abort_refuted_by_abort
           abrt_image abrt_image abrt_entry abrt_entry abrt_input
           abrt_entry_valid abrt_entry_valid
           abrt_input_valid).
  exact (abrt_dies_by_signal source_alloc_limit).
Qed.

(** THE CONTROL, and it is the half that says the refutation above is
    about the ABORT rather than about the image.  The identical program
    is NOT refuted this way with the declaration clear, because with it
    clear [Kernel.Signal.tkill_spec] declines and the run never reaches
    a [State.KillEv] to be refuted by — it leaves the modeled surface
    instead.  So the two stances really do differ on this image, which
    is what [Run.valid_input] pinning [false] is worth. *)
Definition abrt_input_undeclared : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

Lemma abrt_tkill_declined_undeclared :
  check_syscall (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130))
    (mkEffect (Z_to_bv 64 0) [] [])
    (with_tid abort_tid
       (init_model (segments_reserved abrt_segments) abrt_brk abrt_mbase
          abrt_sp source_alloc_limit abrt_input_undeclared))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** THE DATA FLOW, PINNED.  Everything above rests on one claim about the
    program that a reader cannot check by looking at the trace: that
    [tkill]'s first argument is the value the FIRST syscall returned,
    rather than a constant the image carries.  These three say it.

    First, the argument really is the chosen tid at the second [ecall].
    The image contains no 4242: a0 was last written by
    [Run.apply_effect]. *)
Lemma abrt_tkill_pid_is_the_returned_tid :
  in_arg (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130)) 0 = abort_tid.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(** Second, the value was a CHOICE and not a constant: the acceptor
    admits a different tid from the same state, so nothing in the model
    forced 4242.  If [Kernel.Fork.set_tid_address_spec] ever answered a
    fixed value, this would stop holding and the paragraph above would
    stop being true. *)
Lemma abrt_sc1_admits_another_tid : forall lim,
  check_syscall (sys_input abrt_segments (abrt_s 3) (Z_to_bv 64 96))
    (mkEffect (Z_to_bv 64 1234) [] []) (abrt_model lim)
  = CheckOk (with_tid (Z_to_bv 64 1234) (abrt_model lim)) [].
Proof. intros lim. vm_compute. reflexivity. Qed.

(** Third, the match is what the kill DEPENDED on.  The same call, the
    same registers, the same declaration -- and a model whose recorded
    tid is one greater -- is declined rather than fatal.  So the death
    above is not the arm firing at any declared state; it is the arm
    firing because the program sent the signal to ITSELF. *)
Lemma abrt_tkill_other_tid_declined : forall lim,
  check_syscall (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130))
    (mkEffect (Z_to_bv 64 0) [] [])
    (with_tid (Z_to_bv 64 4243) (abrt_model lim))
  = CheckUnmodeled.
Proof. intros lim. vm_compute. reflexivity. Qed.

(* =========================================================================
   The same refutation, in the classifier statement shape
   ========================================================================= *)

(** WHY THIS IS HERE AND NOT ONLY IN THE BASELINE SHAPE.  A classifier
    task is stated over [Run.run_scfg] rather than [Run.run], and the
    abort declaration has a family there too
    ([Equivalence.strong_universal_error_free_T_scfg_abort]).  Its bite
    needs an instance too, for the reason this file
    exists one shape up: a conditional refutation nobody has
    shown fires says nothing about whether the clause it names can ever
    be the one that fails.

    THE TRANSFER IS THE WHOLE PROOF, and it is one behaviour
    equivalence.  At [Run.may_fail_cfg] the filtered run and the plain
    run admit the same traces ([Run.run_scfg_may_fail]), and
    [Equivalence.dies_by_signal] is read off [Run.bh_traces], so it
    transports — which is what
    [Equivalence.dies_by_signal_behavior_equiv] is for.

    WHY [may_fail_cfg] RATHER THAN AN ARBITRARY CONFIGURATION: the
    filter only ever REMOVES executions ([Run.run_scfg_sub_traces]), so
    at a configuration that forces some family the kill could in
    principle be filtered out along with the run that reaches it.  What
    settles whether it is, is whether THIS image issues a syscall that
    configuration can refuse -- a number with no arm in
    [Run.injected_table] has nothing to inject, so no configuration
    refuses it.  This image issues [set_tid_address] and [tkill] and
    nothing else, and neither number is in that table, so no execution
    of it can be filtered and the witness would generalise to any
    configuration.  [may_fail_cfg] is stated because it is what a task
    gets by saying nothing, not because the wider claim would fail. *)
Theorem abrt_dies_by_signal_scfg : forall lim,
  dies_by_signal (run_scfg may_fail_cfg abrt_image lim abrt_entry abrt_input).
Proof.
  intros lim.
  apply (dies_by_signal_behavior_equiv _ _ (run_scfg_may_fail _ _ _ _)).
  exact (abrt_dies_by_signal lim).
Qed.

(** ... and the classifier-shape refutation, fired rather than stated.
    The image is refuted against ITSELF, so the only clause that can
    fail is the one [Equivalence.error_free_unkilled] adds over
    [Equivalence.error_free]: the two runs are the same run, their trace
    sets are equal, and neither takes an error transition -- a followed
    abort is not an error.  That is the weakening the conjunct exists to
    stop, exhibited in the shape a classifier task is actually stated
    in. *)
Theorem abrt_refutes_error_free_scfg_abort :
  ~ strong_universal_error_free_T_scfg_abort may_fail_cfg abrt_image abrt_image.
Proof.
  apply (strong_universal_error_free_T_scfg_abort_refuted_by_abort
           may_fail_cfg abrt_image abrt_image abrt_entry abrt_entry abrt_input
           abrt_entry_valid abrt_entry_valid
           abrt_input_valid).
  exact (abrt_dies_by_signal_scfg source_alloc_limit).
Qed.

(* =========================================================================
   The second path: a launch that already blocks SIGABRT
   ========================================================================= *)

(** WHY A SECOND IMAGE.  [Run.valid_sigmask] forbids only the kernel-only
    bits, so a launch whose mask blocks SIGABRT is a valid input under
    [Run.valid_input_abort].  On such a launch musl's [raise(SIGABRT)]
    RETURNS: [raise] restores the launch mask, which still blocks the
    signal, so nothing is delivered.  [abort] then takes its second path
    (src/exit/abort.c, musl 1.2.6): block every signal, install SIG_DFL
    for SIGABRT, send it again, and unblock it.  The unblock is what kills
    the process ([Kernel.Signal.sigmask_deliver_model]).

    If the model declined any call on that path, every program that can
    reach [abort()] would reach [Run.SError] on the same input under this
    launch, and no error-free statement with the abort declaration could
    be true of it.  [abrt_blocked_error_free] says that no execution of
    the path reaches [Run.SError]; [abrt_blocked_dies_by_signal] says that
    an execution reaches the [State.KillEv], so the first is not true
    only because the run stops early.

    ** The program

    Thirty-five instructions at 0x100, then four bytes of padding, then
    fifty-six bytes of data at 0x190, the syscalls in musl's order:

    #<pre>
      addi a7, x0, 96      06000893   set_tid_address   (musl's __init_tp)
      addi a0, x0, 0       00000513   tidptr = NULL
      ecall                00000073   -> a0 = the tid the model chose
      fmv.d.x f8, a0       f2050453   keep the tid
      addi a7, x0, 135     08700893   rt_sigprocmask    (raise: __block_app_sigs)
      addi a0, x0, 0       00000513   SIG_BLOCK
      addi a1, x0, 0x190   19000593   &app_mask
      addi a2, sp, -8      ff810613   &set
      addi a3, x0, 8       00800693   _NSIG/8
      ecall                00000073   -> set = the launch mask
      fmv.x.d a0, f8       e2040553   the tid
      addi a1, x0, 6       00600593   SIGABRT
      addi a7, x0, 130     08200893   tkill             (raise)
      ecall                00000073   -> pending, because blocked
      addi a7, x0, 135     08700893   rt_sigprocmask    (raise: __restore_sigs)
      addi a0, x0, 2       00200513   SIG_SETMASK
      addi a1, sp, -8      ff810593   &set
      addi a2, x0, 0       00000613   NULL
      ecall                00000073   -> the launch mask: still blocked
      addi a0, x0, 0       00000513   SIG_BLOCK         (abort: __block_all_sigs)
      addi a1, x0, 0x198   19800593   &all_mask
      ecall                00000073
      addi a7, x0, 134     08600893   rt_sigaction      (abort)
      addi a0, x0, 6       00600513   SIGABRT
      addi a1, x0, 0x1a8   1a800593   &(struct k_sigaction){.handler = SIG_DFL}
      ecall                00000073   -> 0               (a2 = NULL, a3 = 8)
      fmv.x.d a0, f8       e2040553   the tid
      addi a1, x0, 6       00600593   SIGABRT
      addi a7, x0, 130     08200893   tkill             (abort)
      ecall                00000073   -> still pending
      addi a7, x0, 135     08700893   rt_sigprocmask    (abort)
      addi a0, x0, 1       00100513   SIG_UNBLOCK
      addi a1, x0, 0x1a0   1a000593   &{1 << (SIGABRT - 1)}
      ecall                00000073   -> killed
      ebreak               00100073   musl's a_crash(): never reached

      0x190  app_mask  0xfffffffc7fffffff   (src/signal/block.c)
      0x198  all_mask  0xffffffffffffffff
      0x1a0  1 << 5
      0x1a8  32 zero bytes: musl's struct k_sigaction with handler SIG_DFL
    #</pre>

    THE TID IS KEPT IN f8, NOT IN AN INTEGER REGISTER, and that is for
    the proof, not for the model.  [Kernel.Fork.set_tid_address_spec]
    lets the tid be any value in its window, so the error-free half is
    proved for a tid [t] that is a variable.  [fmv.d.x] and [fmv.x.d]
    move a register's bits unchanged ([Riscv.Sem]), where an integer copy
    is an addition; so [tkill]'s first argument is [t] itself, and the
    proof needs only that [Syscall.pid32] does not change a [t] in the
    window ([blk_tid_pid32]).  musl reads the tid from memory instead.
    The syscalls and their arguments are musl's, with one exception
    that changes no answer: musl's [__init_tp] passes
    [&__thread_list_lock] to [set_tid_address] (src/env/__init_tls.c,
    musl 1.2.6) where this image passes NULL, and
    [Kernel.Fork.set_tid_address_spec] does not read the pointer.

    THE LAUNCH: [abrt_input] with [State.in_sigmask] = 1 << 5, which is
    SIGABRT's bit and nothing else. *)
Definition abrt_blocked_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 200;
  seg_perms := "r-x"%string;
  seg_bytes := ["930800061305000073000000530405f2930870081305000093050019130681ff9306800073000000530504e29305600093082008730000009308700813052000930581ff130600007300000013050000930580197300000093086008130560009305801a73000000530504e293056000930820087300000093087008130510009305001a730000007300100000000000ffffff7ffcffffffffffffffffffffff20000000000000000000000000000000000000000000000000000000000000000000000000000000"%pstring];
  seg_kind  := SegLoader
|}.
Definition abrt_blocked_segments : list Segment := [abrt_blocked_segment].
Definition abrt_blocked : Image := mkImage abrt_blocked_segments 0x100 demo_phdrs.

Definition abrt_blocked_input : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 32) demo_hwcap true Sv48.

Example abrt_blocked_input_blocks_sigabrt :
  sigabrt_blocked (in_sigmask abrt_blocked_input) = true
  /\ in_abort_terminal abrt_blocked_input = true.
Proof. split; vm_compute; reflexivity. Qed.

(** The launch is valid under the abort declaration: the mask has no
    kernel-only bit, which is all [Run.valid_sigmask] asks. *)
Example abrt_blocked_input_valid : valid_input_abort abrt_blocked_input.
Proof.
  unfold valid_input_abort, abrt_blocked_input, valid_argv, valid_envp.
  cbn [mkProcInput in_argv in_envp in_fs in_execfn].
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try (unfold valid_hwcap; left; reflexivity);
    (* [Fs.fs_image_real], the FIFTH conjunct, as at
       [abrt_input_valid]: the image is empty. *)
    try (unfold fs_image_real; vm_compute; reflexivity);
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | split
                 | cbn; lia | reflexivity | intros [] ].
  all: try valid_urandom_default.
  (* [Run.valid_launch], as at [abrt_input_valid]: the launch name is
     [State.default_execfn], one byte and no NUL, and the launch is
     eleven bytes against the E2BIG limit [bprm_stack_limits]
     (fs/exec.c, Linux v6.18.46, commit 1f99e9ab748f) computes.  The
     blocked mask changes neither half. *)
  all: try (unfold valid_execfn, default_execfn, valid_path_name;
            left; split;
            [ cbn [length]; lia
            | cbn [In]; intros [H | []];
              apply (proj2 (bv_eqb_eq _ _)) in H; vm_compute in H;
              discriminate ]).
  all: try (unfold launch_bytes, e2big_limit, default_execfn;
            cbn [in_argv in_envp in_execfn]; vm_compute; discriminate).
Qed.

(** The entry is [Checks.Examples.demo_entry_of]'s again, valid for
    this image for the reason it is valid for the first one: this
    segment, too, ends inside the first page, so the same break base
    serves and [Run.valid_brk] is the only conjunct the image can
    change.  Quantified over inputs with the entry a function of them,
    for the reason [demo_entry_valid_abrt] is. *)
Example demo_entry_valid_abrt_blocked : forall inp,
  valid_input_abort inp -> valid_entry abrt_blocked (demo_entry_of inp) inp.
Proof.
  intros inp Hvalid.
  red in Hvalid.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  unfold valid_entry, demo_entry_of, abrt_blocked.
  apply launch_entry_va_valid; try assumption.
  unfold valid_brk.
  repeat split; vm_compute; try reflexivity; try discriminate.
Qed.

(** The entry the second image's run is stepped at: the entry of the
    launch it runs on, which is the blocked-mask one. *)
Definition blk_entry : ExecEntry := demo_entry_of abrt_blocked_input.

Lemma blk_entry_valid : valid_entry abrt_blocked blk_entry abrt_blocked_input.
Proof. exact (demo_entry_valid_abrt_blocked _ abrt_blocked_input_valid). Qed.

Definition blk_sp : word := en_sp blk_entry.
Definition blk_brk : word := en_brk blk_entry.
Definition blk_mbase : word := en_mmap_base blk_entry.
Definition blk_draw : EntryDraw := en_draw blk_entry.

Lemma blk_entry_fields :
  blk_entry = mkEntry blk_sp blk_brk blk_mbase blk_draw.
Proof.
  unfold blk_sp, blk_brk, blk_mbase, blk_draw. destruct blk_entry.
  reflexivity.
Qed.

(** ** The legs between the syscalls

    A leg is the run of instructions from one syscall's successor to the
    next [ecall].  As above, the memory of every state on a leg is the
    leg's first state's, because no instruction of this image loads or
    stores; [blk_leg ms k] is the state [k] instructions into the leg
    that starts at [ms]. *)
Definition blk_legk (ms : machine_state) (k : nat) : machine_state :=
  match run_steps k abrt_blocked_segments ms with
  | Some ms' => ms'
  | None => ms
  end.
Definition blk_leg (ms : machine_state) (k : nat) : machine_state :=
  with_mem (blk_legk ms k) (ms_mem ms).

Lemma blk_leg_0 : forall ms, blk_leg ms 0 = ms.
Proof. intros ms. exact (eq_sym (with_mem_eta ms)). Qed.

(** What [vm_compute] proves for each instruction of a leg, with the
    memory a variable: the instruction is not an [ecall] already pending,
    and it steps to the next state. *)
Definition leg_ok (ms : machine_state) (k : nat) : Prop :=
  ms_svc_pending (blk_legk ms k) = None
  /\ forall mem, RiscvSemantics.step abrt_blocked_segments (with_mem (blk_legk ms k) mem)
                 = MachineOk (with_mem (blk_legk ms (S k)) mem).

Lemma leg_instr : forall ms model k,
  m_halted model = None -> m_vm_lazy model = [] -> leg_ok ms k ->
  sstep abrt_blocked_segments (mkCfg (blk_leg ms k) model) []
    (SNext (mkCfg (blk_leg ms (S k)) model))
  /\ (forall evs st, sstep abrt_blocked_segments (mkCfg (blk_leg ms k) model) evs st ->
        evs = [] /\ st = SNext (mkCfg (blk_leg ms (S k)) model)).
Proof.
  intros ms model k Hh Hlazy [Hsvc Hstep]. unfold blk_leg. split.
  - apply sstep_instr; [exact Hh | exact Hsvc |].
    rewrite (mi_account_step_no_lazy _ _ _ Hlazy), Hstep. reflexivity.
  - apply sstep_instr_only; [exact Hlazy | exact Hsvc | apply Hstep].
Qed.

Lemma exec_leg : forall ms model n (Q : post),
  m_halted model = None -> m_vm_lazy model = [] ->
  (forall k, (k < n)%nat -> leg_ok ms k) ->
  exec abrt_blocked_segments (mkCfg (blk_leg ms n) model) Q ->
  exec abrt_blocked_segments (mkCfg (blk_leg ms 0) model) Q.
Proof.
  intros ms model n Q Hh Hlazy Hok Hend.
  assert (H : forall d k, (k + d = n)%nat ->
                exec abrt_blocked_segments (mkCfg (blk_leg ms k) model) Q).
  { induction d as [|d IH]; intros k Hk.
    - replace k with n by lia. exact Hend.
    - destruct (leg_instr ms model k Hh Hlazy (Hok k ltac:(lia))) as [Hs Ho].
      eapply exec_step_only; [exact Hs | exact Ho |].
      exact (IH (S k) ltac:(lia)). }
  exact (H n 0%nat eq_refl).
Qed.

(** ** The syscalls

    Each syscall on the path has exactly one outcome: the checker accepts
    one effect, and two accepted effects are equal.  The second half is
    [check_*_det] below, read off the checkers' arms; nothing in it is
    about this image. *)
Lemma check_ret_only_det : forall e1 e2 r m evs m1 v1 m2 v2,
  check_ret_only e1 r m evs = CheckOk m1 v1 ->
  check_ret_only e2 r m evs = CheckOk m2 v2 -> e1 = e2 /\ m1 = m2 /\ v1 = v2.
Proof.
  intros e1 e2 r m evs m1 v1 m2 v2 H1 H2.
  apply check_ret_only_ok_iff in H1, H2.
  destruct H1 as (-> & -> & ->), H2 as (-> & -> & ->). repeat split.
Qed.

Lemma check_ret_only_copyins_det : forall reads e1 e2 r m evs m1 v1 m2 v2,
  check_ret_only_copyins reads e1 r m evs = CheckOk m1 v1 ->
  check_ret_only_copyins reads e2 r m evs = CheckOk m2 v2 ->
  e1 = e2 /\ m1 = m2 /\ v1 = v2.
Proof.
  intros reads e1 e2 r m evs m1 v1 m2 v2 H1 H2.
  apply check_ret_only_copyins_ok_iff in H1, H2.
  destruct H1 as (-> & -> & ->), H2 as (-> & -> & ->). repeat split.
Qed.

Lemma check_write_oset_det : forall i oset old e1 e2 m m1 v1 m2 v2,
  check_write_oset i oset old e1 m = CheckOk m1 v1 ->
  check_write_oset i oset old e2 m = CheckOk m2 v2 ->
  e1 = e2 /\ m1 = m2 /\ v1 = v2.
Proof.
  intros i oset old e1 e2 m m1 v1 m2 v2 H1 H2.
  unfold check_write_oset in H1, H2.
  destruct (negb (access_okb oset NSIG_BYTES)); cbv beta iota in H1, H2.
  { eapply check_ret_only_det; eassumption. }
  destruct (read_bytes_map (in_wmem i) oset (Z_to_bv 64 NSIG_BYTES));
    cbv beta iota in H1, H2; [|discriminate H1].
  apply check_one_write_ok_iff in H1, H2.
  destruct H1 as (-> & -> & ->), H2 as (-> & -> & ->). repeat split.
Qed.

Lemma check_write_oset_copyins_det : forall reads i oset old e1 e2 m m1 v1 m2 v2,
  check_write_oset_copyins reads i oset old e1 m = CheckOk m1 v1 ->
  check_write_oset_copyins reads i oset old e2 m = CheckOk m2 v2 ->
  e1 = e2 /\ m1 = m2 /\ v1 = v2.
Proof.
  intros reads i oset old e1 e2 m m1 v1 m2 v2 H1 H2.
  unfold check_write_oset_copyins in H1, H2.
  destruct (check_write_oset i oset old (clear_copyins e1) m) eqn:W1;
    try discriminate H1.
  destruct (access_ranges_eqb (eff_copyins e1) reads) eqn:C1; [|discriminate H1].
  injection H1 as <- <-.
  destruct (check_write_oset i oset old (clear_copyins e2) m) eqn:W2;
    try discriminate H2.
  destruct (access_ranges_eqb (eff_copyins e2) reads) eqn:C2; [|discriminate H2].
  injection H2 as <- <-.
  edestruct check_write_oset_det as (Hc & Hm & Hv); [exact W1 | exact W2 |].
  apply access_ranges_eqb_eq in C1, C2.
  split; [| split; assumption].
  destruct e1 as [r1 w1 z1 u1 c1 i1], e2 as [r2 w2 z2 u2 c2 i2].
  cbn in C1, C2. unfold clear_copyins, with_copyins in Hc. cbn in Hc.
  injection Hc as -> -> -> -> ->. subst. reflexivity.
Qed.

Lemma check_send_sigabrt_forced : forall eff m m' evs,
  check_send_sigabrt eff m = CheckOk m' evs ->
  eff = mkEffect (Z_to_bv 64 0) [] [] /\ evs = []
  /\ m' = (if sigabrt_blocked (m_sigmask m) then with_sigabrt_pending m
           else with_killed (Z_to_bv 64 SIGABRT) m).
Proof.
  intros [ret ws zs us cs ci] m m' evs H. unfold check_send_sigabrt in H.
  destruct ws as [|? ?]; [|discriminate H].
  destruct zs as [|? ?]; [|discriminate H].
  destruct us as [|? ?]; [|discriminate H].
  destruct cs as [|? ?]; [|discriminate H].
  destruct ci as [|? ?]; [|discriminate H].
  cbv beta iota in H.
  destruct (negb (bv_eqb ret (Z_to_bv 64 0))) eqn:E; [discriminate H|].
  apply negb_false_iff, bv_eqb_eq in E. subst ret.
  destruct (sigabrt_blocked (m_sigmask m)); injection H as <- <-;
    repeat split.
Qed.

Lemma check_send_sigabrt_det : forall e1 e2 m m1 v1 m2 v2,
  check_send_sigabrt e1 m = CheckOk m1 v1 ->
  check_send_sigabrt e2 m = CheckOk m2 v2 -> e1 = e2 /\ m1 = m2 /\ v1 = v2.
Proof.
  intros e1 e2 m m1 v1 m2 v2 H1 H2.
  apply check_send_sigabrt_forced in H1, H2.
  destruct H1 as (-> & -> & ->), H2 as (-> & -> & ->). repeat split.
Qed.

(** Split every [if] two acceptor runs share, then close the leaf. *)
Ltac det_ifs :=
  repeat match goal with
         | H : context [if ?c then _ else _] |- _ => destruct c; cbv beta iota in *
         end.
Ltac det_leaf :=
  first [ discriminate
        | eapply check_ret_only_det; eassumption
        | eapply check_ret_only_copyins_det; eassumption
        | eapply check_write_oset_det; eassumption
        | eapply check_write_oset_copyins_det; eassumption
        | eapply check_send_sigabrt_det; eassumption ].

Lemma check_rt_sigprocmask_det : forall i how nset oset ss e1 e2 m m1 v1 m2 v2,
  check_rt_sigprocmask i how nset oset ss e1 m = CheckOk m1 v1 ->
  check_rt_sigprocmask i how nset oset ss e2 m = CheckOk m2 v2 ->
  e1 = e2 /\ m1 = m2 /\ v1 = v2.
Proof.
  intros i how nset oset ss e1 e2 m m1 v1 m2 v2 H1 H2.
  unfold check_rt_sigprocmask in H1, H2. cbv zeta in H1, H2.
  det_ifs. all: try det_leaf.
  all: destruct (sigset_at (in_mem i) nset); cbv beta iota in *; det_ifs; det_leaf.
Qed.

Lemma check_rt_sigaction_det : forall i sig act oact ss e1 e2 m m1 v1 m2 v2,
  check_rt_sigaction i sig act oact ss e1 m = CheckOk m1 v1 ->
  check_rt_sigaction i sig act oact ss e2 m = CheckOk m2 v2 ->
  e1 = e2 /\ m1 = m2 /\ v1 = v2.
Proof.
  intros i sig act oact ss e1 e2 m m1 v1 m2 v2 H1 H2.
  unfold check_rt_sigaction in H1, H2.
  det_ifs. all: try det_leaf.
  all: destruct (sigaction_flags (in_mem i) act); cbv beta iota in *; det_ifs; det_leaf.
Qed.

Lemma check_tkill_det : forall pid sig e1 e2 m m1 v1 m2 v2,
  check_tkill pid sig e1 m = CheckOk m1 v1 ->
  check_tkill pid sig e2 m = CheckOk m2 v2 -> e1 = e2 /\ m1 = m2 /\ v1 = v2.
Proof.
  intros pid sig e1 e2 m m1 v1 m2 v2 H1 H2.
  unfold check_tkill, check_tkill_self in H1, H2.
  det_ifs. all: try det_leaf.
  all: destruct (m_tid m); cbv beta iota in *; det_ifs; det_leaf.
Qed.

Lemma check_syscall_tkill_at : forall i eff m,
  bv_unsigned (in_sysno i) = 130%Z ->
  check_syscall i eff m = check_tkill (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

(** A syscall whose checker accepts one effect: the transition, and that
    it is the only one.  [Run.sstep_exit] and [Run.sstep_killed] are
    ruled out by the post-model, and [Run.sstep_syscall_unmodeled] by
    the checker's acceptance. *)
Lemma syscall_step : forall ms model x8 eff0 m0,
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input abrt_blocked_segments ms x8) eff0 model = CheckOk m0 [] ->
  (forall eff m' evs,
     check_syscall (sys_input abrt_blocked_segments ms x8) eff model = CheckOk m' evs ->
     eff = eff0 /\ m' = m0 /\ evs = []) ->
  m_halted m0 = None -> m_killed m0 = None -> m_vm_lazy m0 = [] ->
  sstep abrt_blocked_segments (mkCfg ms model) []
    (SNext (mkCfg (blk_leg (advance_past_svc (apply_effect ms eff0)) 0) m0))
  /\ (forall evs st, sstep abrt_blocked_segments (mkCfg ms model) evs st ->
        evs = [] /\
        st = SNext (mkCfg (blk_leg (advance_past_svc (apply_effect ms eff0)) 0) m0)).
Proof.
  intros ms model x8 eff0 m0 Hh Hsvc Hchk Hdet Hh0 Hk0 Hlazy.
  rewrite blk_leg_0. split.
  - eapply sstep_syscall;
      [ exact Hh | exact Hsvc | apply check_syscall_ok_iff; exact Hchk
      | exact Hh0 | apply materialize_model_accesses_no_lazy; exact Hlazy ].
  - intros evs st Hss. inversion Hss; subst; try congruence.
    all: match goal with
         | H : ms_svc_pending _ = Some ?y |- _ => rewrite Hsvc in H; injection H as <-
         end.
    all: first
      [ match goal with
        | Hs : syscall_spec _ _ Unmodeled |- _ =>
            pose proof (check_syscall_complete_unmodeled _ _ eff0 Hs) as Hc;
            rewrite Hchk in Hc; discriminate Hc
        end
      | match goal with
        | Hs : syscall_spec _ _ (Ok _ _ _) |- _ =>
            apply check_syscall_complete_ok in Hs;
            destruct (Hdet _ _ _ Hs) as (-> & -> & ->)
        end;
        first
          [ match goal with
            | Hm : materialize_model_accesses _ _ = Some _ |- _ =>
                rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hm;
                injection Hm as <-; split; reflexivity
            end
          | match goal with
            | Hm : materialize_model_accesses _ _ = None |- _ =>
                rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hm;
                discriminate Hm
            end
          | congruence ] ].
Qed.

(** ... and the one whose accepted effect kills the process. *)
Lemma syscall_kill_step : forall ms model x8 eff0 m0 sig,
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input abrt_blocked_segments ms x8) eff0 model = CheckOk m0 [] ->
  (forall eff m' evs,
     check_syscall (sys_input abrt_blocked_segments ms x8) eff model = CheckOk m' evs ->
     eff = eff0 /\ m' = m0 /\ evs = []) ->
  m_killed m0 = Some sig -> m_halted m0 <> None ->
  sstep abrt_blocked_segments (mkCfg ms model) [KillEv sig (m_fs m0)] (SNext (mkCfg ms m0))
  /\ (forall evs st, sstep abrt_blocked_segments (mkCfg ms model) evs st ->
        evs = [KillEv sig (m_fs m0)] /\ st = SNext (mkCfg ms m0)).
Proof.
  intros ms model x8 eff0 m0 sig Hh Hsvc Hchk Hdet Hk0 Hh0. split.
  - change [KillEv sig (m_fs m0)] with ([] ++ [KillEv sig (m_fs m0)]).
    eapply sstep_killed;
      [ exact Hh | exact Hsvc | apply check_syscall_ok_iff; exact Hchk | exact Hk0 ].
  - intros evs st Hss. inversion Hss; subst; try congruence.
    all: match goal with
         | H : ms_svc_pending _ = Some ?y |- _ => rewrite Hsvc in H; injection H as <-
         end.
    all: first
      [ match goal with
        | Hs : syscall_spec _ _ Unmodeled |- _ =>
            pose proof (check_syscall_complete_unmodeled _ _ eff0 Hs) as Hc;
            rewrite Hchk in Hc; discriminate Hc
        end
      | match goal with
        | Hs : syscall_spec _ _ (Ok _ _ _) |- _ =>
            apply check_syscall_complete_ok in Hs;
            destruct (Hdet _ _ _ Hs) as (-> & -> & ->)
        end;
        first [ congruence | split; [cbn [app]; congruence | reflexivity] ] ].
Qed.

(** Bounds a tid from [Kernel.Fork.set_tid_address_spec]'s window
    satisfies, which [tkill]'s checks read. *)
Lemma blk_tid_pid32 : forall t,
  (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z -> pid32 t = t.
Proof.
  intros t [H1 H2]. unfold pid32, abi_low32.
  unfold PID_MAX_ENVELOPE in H2. change (2 ^ 22)%Z with 4194304%Z in H2.
  rewrite Z.mod_small by (change (2 ^ 32)%Z with 4294967296%Z; lia).
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma blk_tid_positive : forall t,
  (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z -> pid_positive t = true.
Proof.
  intros t [H1 H2]. unfold pid_positive. cbv zeta.
  unfold PID_MAX_ENVELOPE in H2. change (2 ^ 22)%Z with 4194304%Z in H2.
  change (2 ^ 31)%Z with 2147483648%Z.
  apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Ltac blk_check_eq :=
  vm_compute;
  repeat first [reflexivity | (apply bv_eq; reflexivity) | progress f_equal].

Ltac blk_svc :=
  vm_compute; first [reflexivity | f_equal; apply bv_eq; reflexivity].

(** ** The states and models along the path

    [blk_L1 t] .. [blk_L7 t] are the first states of the legs after the
    first seven syscalls, for the tid [t]; [blk_m1 t lim] .. [blk_m8 t lim]
    are the models after them, except that there is no [blk_m6]:
    [rt_sigaction] leaves [blk_m5] as it is.  The masks are what
    [sigmask_strip] and
    [sigmask_apply] give: [app_mask] and [all_mask] lose SIGKILL's and
    SIGSTOP's bits (1 << 8, 1 << 18). *)
Definition blk_L0 : machine_state :=
  init_machine_state abrt_blocked_segments 0x100 demo_phdrs blk_sp blk_mbase
    blk_draw abrt_blocked_input.

Definition blk_m0 (lim : Z) : Model :=
  init_model (segments_reserved abrt_blocked_segments) blk_brk blk_mbase
    blk_sp lim abrt_blocked_input.
Definition blk_c (lim : Z) : config := mkCfg (blk_leg blk_L0 0) (blk_m0 lim).

Lemma blk_config : forall lim,
  init_config abrt_blocked_segments 0x100 demo_phdrs blk_sp blk_brk
    blk_mbase blk_draw lim abrt_blocked_input
  = blk_c lim.
Proof. intros lim. unfold blk_c. rewrite blk_leg_0. reflexivity. Qed.

(** The effects: the old mask written to [set] (eight bytes, 1 << 5),
    the eight bytes of each [sigset_t] the kernel read, and the 24 bytes
    of the [struct k_sigaction] that [rt_sigaction] read.  [set] is the
    eight bytes below the entry stack pointer, which is where the image
    puts it with [addi a2, sp, -8], so the address is read off
    [blk_sp] rather than written out. *)
Definition blk_set_addr : word := Z_to_bv 64 (bv_unsigned blk_sp - 8).

Definition blk_e2 : SyscallEffect :=
  with_copyins [(Z_to_bv 64 0x190, 8%nat)]
    (mkEffect (Z_to_bv 64 0) [(blk_set_addr, Z_to_le_bytes 8 32)] []).
Definition blk_e0 : SyscallEffect := mkEffect (Z_to_bv 64 0) [] [].
Definition blk_e4 : SyscallEffect :=
  with_copyins [(blk_set_addr, 8%nat)] (mkEffect (Z_to_bv 64 0) [] []).
Definition blk_e5 : SyscallEffect :=
  with_copyins [(Z_to_bv 64 0x198, 8%nat)] (mkEffect (Z_to_bv 64 0) [] []).
Definition blk_e6 : SyscallEffect :=
  with_copyins [(Z_to_bv 64 0x1a8, 24%nat)] (mkEffect (Z_to_bv 64 0) [] []).
Definition blk_e8 : SyscallEffect :=
  with_copyins [(Z_to_bv 64 0x1a0, 8%nat)] (mkEffect (Z_to_bv 64 0) [] []).

Definition blk_L1 (t : word) : machine_state :=
  advance_past_svc (apply_effect (blk_leg blk_L0 3) (mkEffect t [] [])).
Definition blk_L2 (t : word) : machine_state :=
  advance_past_svc (apply_effect (blk_leg (blk_L1 t) 7) blk_e2).
Definition blk_L3 (t : word) : machine_state :=
  advance_past_svc (apply_effect (blk_leg (blk_L2 t) 4) blk_e0).
Definition blk_L4 (t : word) : machine_state :=
  advance_past_svc (apply_effect (blk_leg (blk_L3 t) 5) blk_e4).
Definition blk_L5 (t : word) : machine_state :=
  advance_past_svc (apply_effect (blk_leg (blk_L4 t) 3) blk_e5).
Definition blk_L6 (t : word) : machine_state :=
  advance_past_svc (apply_effect (blk_leg (blk_L5 t) 4) blk_e6).
Definition blk_L7 (t : word) : machine_state :=
  advance_past_svc (apply_effect (blk_leg (blk_L6 t) 4) blk_e0).

Definition blk_m1 (t : word) (lim : Z) : Model := with_tid t (blk_m0 lim).
(** SIG_BLOCK app_mask over the launch mask 1 << 5. *)
Definition blk_m2 (t : word) (lim : Z) : Model :=
  with_sigmask (Z_to_bv 64 0xfffffffc7ffbfeff) (blk_m1 t lim).
(** tkill with SIGABRT blocked: pending. *)
Definition blk_m3 (t : word) (lim : Z) : Model := with_sigabrt_pending (blk_m2 t lim).
(** SIG_SETMASK back to the launch mask, which still blocks it. *)
Definition blk_m4 (t : word) (lim : Z) : Model :=
  with_sigmask (Z_to_bv 64 32) (blk_m3 t lim).
(** SIG_BLOCK all_mask; [rt_sigaction] leaves this model as it is. *)
Definition blk_m5 (t : word) (lim : Z) : Model :=
  with_sigmask (Z_to_bv 64 0xfffffffffffbfeff) (blk_m4 t lim).
(** tkill again: pending already. *)
Definition blk_m7 (t : word) (lim : Z) : Model := with_sigabrt_pending (blk_m5 t lim).
(** SIG_UNBLOCK SIGABRT: the pending signal is delivered, and kills. *)
Definition blk_m8 (t : word) (lim : Z) : Model :=
  with_killed (Z_to_bv 64 SIGABRT)
    (with_sigmask (Z_to_bv 64 0xfffffffffffbfedf) (blk_m7 t lim)).

Lemma blk_leg0_ok : forall k, (k < 3)%nat -> leg_ok blk_L0 k.
Proof.
  intros k Hk.
  do 3 (destruct k as [| k];
        [split; [vm_compute; reflexivity | intros mem; vm_compute; reflexivity] |]).
  lia.
Qed.
Lemma blk_leg1_ok : forall t k, (k < 7)%nat -> leg_ok (blk_L1 t) k.
Proof.
  intros t k Hk.
  do 7 (destruct k as [| k];
        [split; [vm_compute; reflexivity | intros mem; vm_compute; reflexivity] |]).
  lia.
Qed.
Lemma blk_leg2_ok : forall t k, (k < 4)%nat -> leg_ok (blk_L2 t) k.
Proof.
  intros t k Hk.
  do 4 (destruct k as [| k];
        [split; [vm_compute; reflexivity | intros mem; vm_compute; reflexivity] |]).
  lia.
Qed.
Lemma blk_leg3_ok : forall t k, (k < 5)%nat -> leg_ok (blk_L3 t) k.
Proof.
  intros t k Hk.
  do 5 (destruct k as [| k];
        [split; [vm_compute; reflexivity | intros mem; vm_compute; reflexivity] |]).
  lia.
Qed.
Lemma blk_leg4_ok : forall t k, (k < 3)%nat -> leg_ok (blk_L4 t) k.
Proof.
  intros t k Hk.
  do 3 (destruct k as [| k];
        [split; [vm_compute; reflexivity | intros mem; vm_compute; reflexivity] |]).
  lia.
Qed.
Lemma blk_leg5_ok : forall t k, (k < 4)%nat -> leg_ok (blk_L5 t) k.
Proof.
  intros t k Hk.
  do 4 (destruct k as [| k];
        [split; [vm_compute; reflexivity | intros mem; vm_compute; reflexivity] |]).
  lia.
Qed.
Lemma blk_leg6_ok : forall t k, (k < 4)%nat -> leg_ok (blk_L6 t) k.
Proof.
  intros t k Hk.
  do 4 (destruct k as [| k];
        [split; [vm_compute; reflexivity | intros mem; vm_compute; reflexivity] |]).
  lia.
Qed.
Lemma blk_leg7_ok : forall t k, (k < 4)%nat -> leg_ok (blk_L7 t) k.
Proof.
  intros t k Hk.
  do 4 (destruct k as [| k];
        [split; [vm_compute; reflexivity | intros mem; vm_compute; reflexivity] |]).
  lia.
Qed.

(** set_tid_address: the one branching step.  Every tid in the window is
    an outcome, and nothing else is. *)
Lemma blk_sc1 : forall lim,
  sstep abrt_blocked_segments (mkCfg (blk_leg blk_L0 3) (blk_m0 lim)) []
    (SNext (mkCfg (blk_leg (blk_L1 abort_tid) 0) (blk_m1 abort_tid lim)))
  /\ (forall evs st,
        sstep abrt_blocked_segments (mkCfg (blk_leg blk_L0 3) (blk_m0 lim)) evs st ->
        evs = [] /\ exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z
                             /\ st = SNext (mkCfg (blk_leg (blk_L1 t) 0) (blk_m1 t lim))).
Proof.
  intros lim.
  assert (Hsvc : ms_svc_pending (blk_leg blk_L0 3) = Some (Z_to_bv 64 96)) by blk_svc.
  assert (Hchk : forall t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z ->
            check_syscall (sys_input abrt_blocked_segments (blk_leg blk_L0 3) (Z_to_bv 64 96))
              (mkEffect t [] []) (blk_m0 lim) = CheckOk (blk_m1 t lim) []).
  { intros t [H1 H2]. rewrite check_syscall_set_tid_address by reflexivity.
    unfold check_set_tid_address. change (m_tid (blk_m0 lim)) with (@None word).
    cbv beta iota.
    rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_lt _ _) H2). reflexivity. }
  assert (Habort : (0 < bv_unsigned abort_tid < PID_MAX_ENVELOPE)%Z)
    by (vm_compute; split; reflexivity).
  assert (Hforced : forall eff m' evs,
            check_syscall (sys_input abrt_blocked_segments (blk_leg blk_L0 3) (Z_to_bv 64 96))
              eff (blk_m0 lim) = CheckOk m' evs ->
            exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z
                      /\ eff = mkEffect t [] [] /\ m' = blk_m1 t lim /\ evs = []).
  { intros [ret ws zs us cs ci] m' evs H.
    rewrite check_syscall_set_tid_address in H by reflexivity.
    unfold check_set_tid_address in H.
    destruct ws as [|? ?]; [|discriminate H].
    destruct zs as [|? ?]; [|discriminate H].
    destruct us as [|? ?]; [|discriminate H].
    destruct cs as [|? ?]; [|discriminate H].
    destruct ci as [|? ?]; [|discriminate H].
    change (m_tid (blk_m0 lim)) with (@None word) in H. cbv beta iota in H.
    destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z) eqn:Eb;
      [|discriminate H].
    injection H as <- <-.
    apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1, E2.
    exists ret. repeat split; assumption. }
  split.
  - rewrite blk_leg_0.
    eapply sstep_syscall;
      [ reflexivity | exact Hsvc | apply check_syscall_ok_iff; exact (Hchk _ Habort)
      | reflexivity | apply materialize_model_accesses_no_lazy; reflexivity ].
  - intros evs st Hss. inversion Hss; subst; try congruence.
    all: match goal with
         | H : ms_svc_pending _ = Some ?y |- _ => rewrite Hsvc in H; injection H as <-
         end.
    all: first
      [ match goal with
        | Hs : syscall_spec _ _ Unmodeled |- _ =>
            pose proof (check_syscall_complete_unmodeled _ _ (mkEffect abort_tid [] []) Hs)
              as Hc;
            rewrite (Hchk _ Habort) in Hc; discriminate Hc
        end
      | match goal with
        | Hs : syscall_spec _ _ (Ok _ _ _) |- _ =>
            apply check_syscall_complete_ok in Hs;
            destruct (Hforced _ _ _ Hs) as (t & Ht & -> & -> & ->)
        end;
        first
          [ match goal with
            | Hm : materialize_model_accesses _ _ = Some _ |- _ =>
                rewrite materialize_model_accesses_no_lazy in Hm by reflexivity;
                injection Hm as <-; split; [reflexivity|];
                exists t; split; [exact Ht | rewrite blk_leg_0; reflexivity]
            end
          | match goal with
            | Hm : materialize_model_accesses _ _ = None |- _ =>
                rewrite materialize_model_accesses_no_lazy in Hm by reflexivity;
                discriminate Hm
            end
          | match goal with
            | Hx : m_halted (blk_m1 _ _) = Some _ |- _ =>
                first [discriminate Hx | vm_compute in Hx; discriminate Hx]
            | Hx : m_killed (blk_m1 _ _) = Some _ |- _ =>
                first [discriminate Hx | vm_compute in Hx; discriminate Hx]
            end ] ].
Qed.

(** rt_sigprocmask(SIG_BLOCK, app_mask, &set, 8): the mask grows, and the
    launch mask is written to [set]. *)
Lemma blk_sc2 : forall lim t,
  sstep abrt_blocked_segments (mkCfg (blk_leg (blk_L1 t) 7) (blk_m1 t lim)) []
    (SNext (mkCfg (blk_leg (blk_L2 t) 0) (blk_m2 t lim)))
  /\ (forall evs st,
        sstep abrt_blocked_segments (mkCfg (blk_leg (blk_L1 t) 7) (blk_m1 t lim)) evs st ->
        evs = [] /\ st = SNext (mkCfg (blk_leg (blk_L2 t) 0) (blk_m2 t lim))).
Proof.
  intros lim t.
  assert (Hsvc : ms_svc_pending (blk_leg (blk_L1 t) 7) = Some (Z_to_bv 64 135)) by blk_svc.
  assert (Hchk : check_syscall
            (sys_input abrt_blocked_segments (blk_leg (blk_L1 t) 7) (Z_to_bv 64 135))
            blk_e2 (blk_m1 t lim) = CheckOk (blk_m2 t lim) []) by blk_check_eq.
  eapply syscall_step;
    [ reflexivity | exact Hsvc | exact Hchk | | reflexivity | reflexivity | reflexivity ].
  intros eff m' evs H. pose proof Hchk as Hc.
  rewrite check_syscall_rt_sigprocmask in H, Hc by reflexivity.
  eapply check_rt_sigprocmask_det; eassumption.
Qed.

(** tkill(tid, SIGABRT) with SIGABRT blocked: pending, and the run goes
    on. *)
Lemma blk_sc3 : forall lim t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z ->
  sstep abrt_blocked_segments (mkCfg (blk_leg (blk_L2 t) 4) (blk_m2 t lim)) []
    (SNext (mkCfg (blk_leg (blk_L3 t) 0) (blk_m3 t lim)))
  /\ (forall evs st,
        sstep abrt_blocked_segments (mkCfg (blk_leg (blk_L2 t) 4) (blk_m2 t lim)) evs st ->
        evs = [] /\ st = SNext (mkCfg (blk_leg (blk_L3 t) 0) (blk_m3 t lim))).
Proof.
  intros lim t Ht.
  assert (Hsvc : ms_svc_pending (blk_leg (blk_L2 t) 4) = Some (Z_to_bv 64 130)) by blk_svc.
  assert (Hchk : check_syscall
            (sys_input abrt_blocked_segments (blk_leg (blk_L2 t) 4) (Z_to_bv 64 130))
            blk_e0 (blk_m2 t lim) = CheckOk (blk_m3 t lim) []).
  { rewrite check_syscall_tkill_at by reflexivity.
    assert (Ha0 : in_arg (sys_input abrt_blocked_segments (blk_leg (blk_L2 t) 4)
                            (Z_to_bv 64 130)) 0 = t) by (vm_compute; reflexivity).
    rewrite Ha0, (blk_tid_pid32 t Ht).
    unfold check_tkill, check_tkill_self. rewrite (blk_tid_positive t Ht).
    change (m_tid (blk_m2 t lim)) with (Some t). cbv beta iota.
    rewrite bv_eqb_refl. blk_check_eq. }
  eapply syscall_step;
    [ reflexivity | exact Hsvc | exact Hchk | | reflexivity | reflexivity | reflexivity ].
  intros eff m' evs H. pose proof Hchk as Hc.
  rewrite check_syscall_tkill_at in H, Hc by reflexivity.
  eapply check_tkill_det; eassumption.
Qed.

(** rt_sigprocmask(SIG_SETMASK, &set, NULL, 8): the launch mask again,
    read back from [set].  SIGABRT stays blocked, so nothing is
    delivered and [raise] returns. *)
Lemma blk_sc4 : forall lim t,
  sstep abrt_blocked_segments (mkCfg (blk_leg (blk_L3 t) 5) (blk_m3 t lim)) []
    (SNext (mkCfg (blk_leg (blk_L4 t) 0) (blk_m4 t lim)))
  /\ (forall evs st,
        sstep abrt_blocked_segments (mkCfg (blk_leg (blk_L3 t) 5) (blk_m3 t lim)) evs st ->
        evs = [] /\ st = SNext (mkCfg (blk_leg (blk_L4 t) 0) (blk_m4 t lim))).
Proof.
  intros lim t.
  assert (Hsvc : ms_svc_pending (blk_leg (blk_L3 t) 5) = Some (Z_to_bv 64 135)) by blk_svc.
  assert (Hchk : check_syscall
            (sys_input abrt_blocked_segments (blk_leg (blk_L3 t) 5) (Z_to_bv 64 135))
            blk_e4 (blk_m3 t lim) = CheckOk (blk_m4 t lim) []) by blk_check_eq.
  eapply syscall_step;
    [ reflexivity | exact Hsvc | exact Hchk | | reflexivity | reflexivity | reflexivity ].
  intros eff m' evs H. pose proof Hchk as Hc.
  rewrite check_syscall_rt_sigprocmask in H, Hc by reflexivity.
  eapply check_rt_sigprocmask_det; eassumption.
Qed.

(** rt_sigprocmask(SIG_BLOCK, all_mask, NULL, 8): abort's second path
    begins. *)
Lemma blk_sc5 : forall lim t,
  sstep abrt_blocked_segments (mkCfg (blk_leg (blk_L4 t) 3) (blk_m4 t lim)) []
    (SNext (mkCfg (blk_leg (blk_L5 t) 0) (blk_m5 t lim)))
  /\ (forall evs st,
        sstep abrt_blocked_segments (mkCfg (blk_leg (blk_L4 t) 3) (blk_m4 t lim)) evs st ->
        evs = [] /\ st = SNext (mkCfg (blk_leg (blk_L5 t) 0) (blk_m5 t lim))).
Proof.
  intros lim t.
  assert (Hsvc : ms_svc_pending (blk_leg (blk_L4 t) 3) = Some (Z_to_bv 64 135)) by blk_svc.
  assert (Hchk : check_syscall
            (sys_input abrt_blocked_segments (blk_leg (blk_L4 t) 3) (Z_to_bv 64 135))
            blk_e5 (blk_m4 t lim) = CheckOk (blk_m5 t lim) []) by blk_check_eq.
  eapply syscall_step;
    [ reflexivity | exact Hsvc | exact Hchk | | reflexivity | reflexivity | reflexivity ].
  intros eff m' evs H. pose proof Hchk as Hc.
  rewrite check_syscall_rt_sigprocmask in H, Hc by reflexivity.
  eapply check_rt_sigprocmask_det; eassumption.
Qed.

(** rt_sigaction(SIGABRT, &{.handler = SIG_DFL}, NULL, 8): THE CALL THIS
    IMAGE EXISTS FOR.  [Kernel.Signal.rt_sigaction_spec] answers it 0,
    records the 24 bytes it read at 0x1a8, and changes nothing else
    ([Kernel.Signal.sigabrt_dfl_install]). *)
Lemma blk_sc6 : forall lim t,
  sstep abrt_blocked_segments (mkCfg (blk_leg (blk_L5 t) 4) (blk_m5 t lim)) []
    (SNext (mkCfg (blk_leg (blk_L6 t) 0) (blk_m5 t lim)))
  /\ (forall evs st,
        sstep abrt_blocked_segments (mkCfg (blk_leg (blk_L5 t) 4) (blk_m5 t lim)) evs st ->
        evs = [] /\ st = SNext (mkCfg (blk_leg (blk_L6 t) 0) (blk_m5 t lim))).
Proof.
  intros lim t.
  assert (Hsvc : ms_svc_pending (blk_leg (blk_L5 t) 4) = Some (Z_to_bv 64 134)) by blk_svc.
  assert (Hchk : check_syscall
            (sys_input abrt_blocked_segments (blk_leg (blk_L5 t) 4) (Z_to_bv 64 134))
            blk_e6 (blk_m5 t lim) = CheckOk (blk_m5 t lim) []) by blk_check_eq.
  eapply syscall_step;
    [ reflexivity | exact Hsvc | exact Hchk | | reflexivity | reflexivity | reflexivity ].
  intros eff m' evs H. pose proof Hchk as Hc.
  rewrite check_syscall_rt_sigaction in H, Hc by reflexivity.
  eapply check_rt_sigaction_det; eassumption.
Qed.

(** tkill(tid, SIGABRT) again: still blocked, still pending. *)
Lemma blk_sc7 : forall lim t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z ->
  sstep abrt_blocked_segments (mkCfg (blk_leg (blk_L6 t) 4) (blk_m5 t lim)) []
    (SNext (mkCfg (blk_leg (blk_L7 t) 0) (blk_m7 t lim)))
  /\ (forall evs st,
        sstep abrt_blocked_segments (mkCfg (blk_leg (blk_L6 t) 4) (blk_m5 t lim)) evs st ->
        evs = [] /\ st = SNext (mkCfg (blk_leg (blk_L7 t) 0) (blk_m7 t lim))).
Proof.
  intros lim t Ht.
  assert (Hsvc : ms_svc_pending (blk_leg (blk_L6 t) 4) = Some (Z_to_bv 64 130)) by blk_svc.
  assert (Hchk : check_syscall
            (sys_input abrt_blocked_segments (blk_leg (blk_L6 t) 4) (Z_to_bv 64 130))
            blk_e0 (blk_m5 t lim) = CheckOk (blk_m7 t lim) []).
  { rewrite check_syscall_tkill_at by reflexivity.
    assert (Ha0 : in_arg (sys_input abrt_blocked_segments (blk_leg (blk_L6 t) 4)
                            (Z_to_bv 64 130)) 0 = t) by (vm_compute; reflexivity).
    rewrite Ha0, (blk_tid_pid32 t Ht).
    unfold check_tkill, check_tkill_self. rewrite (blk_tid_positive t Ht).
    change (m_tid (blk_m5 t lim)) with (Some t). cbv beta iota.
    rewrite bv_eqb_refl. blk_check_eq. }
  eapply syscall_step;
    [ reflexivity | exact Hsvc | exact Hchk | | reflexivity | reflexivity | reflexivity ].
  intros eff m' evs H. pose proof Hchk as Hc.
  rewrite check_syscall_tkill_at in H, Hc by reflexivity.
  eapply check_tkill_det; eassumption.
Qed.

(** rt_sigprocmask(SIG_UNBLOCK, {SIGABRT}, NULL, 8): the pending SIGABRT
    is delivered, at SIG_DFL, and the process dies. *)
Lemma blk_sc8 : forall lim t,
  sstep abrt_blocked_segments (mkCfg (blk_leg (blk_L7 t) 4) (blk_m7 t lim))
    [KillEv (Z_to_bv 64 SIGABRT) (m_fs (blk_m8 t lim))]
    (SNext (mkCfg (blk_leg (blk_L7 t) 4) (blk_m8 t lim)))
  /\ (forall evs st,
        sstep abrt_blocked_segments (mkCfg (blk_leg (blk_L7 t) 4) (blk_m7 t lim)) evs st ->
        evs = [KillEv (Z_to_bv 64 SIGABRT) (m_fs (blk_m8 t lim))]
        /\ st = SNext (mkCfg (blk_leg (blk_L7 t) 4) (blk_m8 t lim))).
Proof.
  intros lim t.
  assert (Hsvc : ms_svc_pending (blk_leg (blk_L7 t) 4) = Some (Z_to_bv 64 135)) by blk_svc.
  assert (Hchk : check_syscall
            (sys_input abrt_blocked_segments (blk_leg (blk_L7 t) 4) (Z_to_bv 64 135))
            blk_e8 (blk_m7 t lim) = CheckOk (blk_m8 t lim) []) by blk_check_eq.
  eapply syscall_kill_step;
    [ reflexivity | exact Hsvc | exact Hchk | | reflexivity
    | intro Hx; vm_compute in Hx; discriminate Hx ].
  intros eff m' evs H. pose proof Hchk as Hc.
  rewrite check_syscall_rt_sigprocmask in H, Hc by reflexivity.
  eapply check_rt_sigprocmask_det; eassumption.
Qed.

(** ** Every execution, followed to its end

    One [OmniRun.exec] judgment gives both theorems: every maximal
    execution ends without an error and with a [State.KillEv] in its
    trace, and [exec] also says that such an execution exists. *)
Definition blk_post : post :=
  fun tr o => ~ is_error o /\ exists sig fs, In (KillEv sig fs) tr.

Lemma blk_exec_after_tid : forall lim t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z ->
  exec abrt_blocked_segments (mkCfg (blk_leg (blk_L1 t) 0) (blk_m1 t lim)) blk_post.
Proof.
  intros lim t Ht.
  eapply exec_leg; [reflexivity | reflexivity | exact (blk_leg1_ok t) |].
  destruct (blk_sc2 lim t) as [S2 O2]. eapply exec_step_only; [exact S2 | exact O2 |].
  eapply exec_leg; [reflexivity | reflexivity | exact (blk_leg2_ok t) |].
  destruct (blk_sc3 lim t Ht) as [S3 O3]. eapply exec_step_only; [exact S3 | exact O3 |].
  eapply exec_leg; [reflexivity | reflexivity | exact (blk_leg3_ok t) |].
  destruct (blk_sc4 lim t) as [S4 O4]. eapply exec_step_only; [exact S4 | exact O4 |].
  eapply exec_leg; [reflexivity | reflexivity | exact (blk_leg4_ok t) |].
  destruct (blk_sc5 lim t) as [S5 O5]. eapply exec_step_only; [exact S5 | exact O5 |].
  eapply exec_leg; [reflexivity | reflexivity | exact (blk_leg5_ok t) |].
  destruct (blk_sc6 lim t) as [S6 O6]. eapply exec_step_only; [exact S6 | exact O6 |].
  eapply exec_leg; [reflexivity | reflexivity | exact (blk_leg6_ok t) |].
  destruct (blk_sc7 lim t Ht) as [S7 O7]. eapply exec_step_only; [exact S7 | exact O7 |].
  eapply exec_leg; [reflexivity | reflexivity | exact (blk_leg7_ok t) |].
  destruct (blk_sc8 lim t) as [S8 O8]. eapply exec_step_only; [exact S8 | exact O8 |].
  apply exec_halt; [intro Hx; vm_compute in Hx; discriminate Hx |].
  cbv beta. unfold blk_post. split; [intros [] |].
  exists (Z_to_bv 64 SIGABRT), (m_fs (blk_m8 t lim)).
  cbn [app In]. left. reflexivity.
Qed.

Lemma blk_exec : forall lim, exec abrt_blocked_segments (blk_c lim) blk_post.
Proof.
  intros lim. unfold blk_c.
  eapply exec_leg; [reflexivity | reflexivity | exact blk_leg0_ok |].
  destruct (blk_sc1 lim) as [S1 O1].
  apply exec_step.
  - reflexivity.
  - do 2 eexists. exact S1.
  - intros evs H. destruct (O1 _ _ H) as (_ & t & _ & Habs). discriminate Habs.
  - intros evs c' H. destruct (O1 _ _ H) as (-> & t & Ht & Hst).
    injection Hst as ->. exact (blk_exec_after_tid lim t Ht).
Qed.

(** THE LAUNCH THAT BLOCKS SIGABRT DOES NOT TAKE THE RUN OFF THE MODEL.
    No execution reaches [Run.SError], for every budget: the tid is
    any value [Kernel.Fork.set_tid_address_spec] allows, and the
    [rt_sigaction] on abort's second path is answered. *)
Theorem abrt_blocked_error_free : forall lim,
  error_free (run abrt_blocked lim blk_entry abrt_blocked_input).
Proof.
  intros lim. unfold error_free.
  rewrite blk_entry_fields. cbn [run bh_errors abrt_blocked].
  rewrite blk_config. apply exec_no_error.
  eapply exec_conseq; [exact (blk_exec lim) |]. intros tr o [H _]. exact H.
Qed.

(** ... and the run ends where Linux's does: death by SIGABRT. *)
Theorem abrt_blocked_dies_by_signal : forall lim,
  dies_by_signal (run abrt_blocked lim blk_entry abrt_blocked_input).
Proof.
  intros lim. rewrite blk_entry_fields.
  cbn [run bh_traces abrt_blocked]. rewrite blk_config.
  destruct (exec_realizes _ _ _ (blk_exec lim)) as (tr & o & Hm & Hne & sig & fs & Hin).
  destruct o as [c | c]; [| exfalso; exact (Hne I)].
  destruct (mexec_halt_star _ _ _ _ Hm c eq_refl) as [Hstar _].
  exists tr, sig, fs. split; [| exact Hin].
  exists tr, c. split; [exact Hstar | apply is_prefix_refl].
Qed.
