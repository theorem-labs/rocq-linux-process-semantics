(** * LinuxProcessSem.Run — Kleene-star trace semantics and trace equivalence

    TRUST BOUNDARY: this file is part of the trusted specification.

    Machine words are [bv 64], bytes are [bv 8], and the segment/stack
    range arithmetic is in [Z] over unsigned values.  [machine_state]
    carries an LR/SC reservation field [ms_resv] (initialized [None];
    cleared on each system call return, as Linux clears it — see
    [advance_past_svc]).

    A binary's observable behavior is its set of finite trace prefixes
    plus TWO error facts: whether SOME execution can reach the explicit
    error transition ([reaches_error]), and whether ALL executions must
    reach it ([all_traces_error]).  Equivalence is equality of prefix
    sets (with an escape only when all source executions error — see
    [Equivalence.equiv]).  For the TARGET an error is fatal
    ([Equivalence.equiv] requires the target error-free).  For the
    SOURCE, the vacuity escape applies only when [all_traces_error]
    proves that EVERY nondeterministic execution reaches error; one
    erroring resolution is not enough when another resolution exits or
    runs forever without error.

    A behavior additionally records [reaches_unmodeled]: whether the run
    can reach a configuration where THIS MODEL gave up, as opposed to one
    where the PROGRAM died.  The two are distinct — [MachineFault] and
    [MachineUnmodeled] on the machine side, and on the syscall side an
    errno-returning [Ok] versus the fail-closed [Unmodeled] — and the source
    side of [Equivalence.strong_equiv] requires the model to cover the
    source everywhere, so that its equivalence claim cannot be satisfied
    by a semantics too weak to follow the binary. *)

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(* =========================================================================
   Trace prefixes and observable behaviors
   ========================================================================= *)

Fixpoint is_prefix {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x = y /\ is_prefix xs ys
  end.

Lemma is_prefix_refl {A} : forall (l : list A), is_prefix l l.
Proof. induction l; cbn; auto. Qed.

Lemma is_prefix_nil {A} : forall (l : list A), is_prefix [] l.
Proof. destruct l; cbn; auto. Qed.

Lemma is_prefix_trans {A} : forall (l1 l2 l3 : list A),
  is_prefix l1 l2 -> is_prefix l2 l3 -> is_prefix l1 l3.
Proof.
  induction l1 as [|x l1 IH]; cbn; [auto|].
  destruct l2 as [|y l2]; cbn; [contradiction|].
  destruct l3 as [|z l3]; cbn; [contradiction|].
  intros [-> H1] [-> H2]; eauto.
Qed.

Lemma is_prefix_app {A} : forall (l1 l2 : list A), is_prefix l1 (l1 ++ l2).
Proof. induction l1; cbn; auto. Qed.

(** Everything observable about one binary on one input: its finite
    trace prefixes, whether it CAN reach the error transition, whether
    EVERY execution MUST reach the error transition, and whether it can
    reach a place where THIS MODEL — rather than the program — gave up.
    The two error propositions deliberately have different quantifiers:
    the source escape consumes [bh_all_errors], while target safety
    consumes [~ bh_errors].

    [bh_unmodeled] is not an observation about the program at all; it is
    an observation about the semantics' COVERAGE of the program, and it
    is what the [modeled] clause of [Equivalence.strong_equiv] rules out
    for the source.  It is a strict sub-case of [bh_errors]: everything
    unmodeled errors, but not everything that errors is unmodeled (see
    [reaches_unmodeled_reaches_error]). *)
Record behavior := mkBehavior {
  bh_traces : list event -> Prop;
  bh_errors : Prop;
  bh_all_errors : Prop;
  bh_unmodeled : Prop;
}.

(* =========================================================================
   Applying a chosen syscall effect to the machine
   ========================================================================= *)

(** The decoded syscall argument registers a0..a5 at the [ecall]. *)
Definition syscall_args (ms : machine_state) : list word :=
  [ms_gpr ms 0; ms_gpr ms 1; ms_gpr ms 2; ms_gpr ms 3; ms_gpr ms 4; ms_gpr ms 5].

Fixpoint apply_writes (mem : word -> option byte) (ws : list (word * list byte))
    : word -> option byte :=
  match ws with
  | [] => mem
  | (a, bs) :: r => apply_writes (write_to_mem mem a bs) r
  end.

(** Is [a] inside one of the (base, size) ranges?  Computed in [Z] over
    unsigned values (grant ranges never wrap; see Specs.v). *)
Definition zeros_cover (zs : list (word * word)) (a : word) : bool :=
  existsb (fun z => Z.leb (bv_unsigned (fst z)) (bv_unsigned a)
                    && Z.ltb (bv_unsigned a)
                             (bv_unsigned (fst z) + bv_unsigned (snd z))) zs.

(** Zero-fill the effect's granted ranges (anonymous mmap/brk memory):
    every covered address reads as byte 0, REPLACING whatever was
    there.  Kept as a functional overlay so multi-megabyte grants never
    materialize byte lists. *)
Definition apply_zeros (mem : word -> option byte) (zs : list (word * word))
    : word -> option byte :=
  match zs with
  | [] => mem
  | _ => fun a => if zeros_cover zs a then Some (Z_to_bv 8 0) else mem a
  end.

(** Erase the effect's inaccessible ranges (munmap, a PROT_NONE
    mapping, mremap, or the tail a brk shrink frees — see
    [State.eff_unmaps]): every covered address becomes UNMAPPED in the
    writable overlay, so a later load faults instead of reading stale
    bytes, as on Linux.  The SPECS only unmap recorded anonymous mappings,
    their subranges, or ranges of them and free pages, disjoint from every
    loaded segment and from the stack, so erasing the overlay really makes the range inaccessible
    (there is no segment underneath for reads to fall back to). *)
Definition apply_unmaps (mem : word -> option byte) (us : list (word * word))
    : word -> option byte :=
  match us with
  | [] => mem
  | _ => fun a => if zeros_cover us a then None else mem a
  end.

(** Apply symbolic copies against an immutable snapshot of the memory from
    BEFORE this syscall effect.  Destination ranges use list order (later
    copies override earlier ones); every source read uses [before], never a
    range already zeroed, copied, or unmapped by the effect. *)
Definition apply_copy (before mem : word -> option byte) (c : MemCopy)
    : word -> option byte :=
  fun a =>
    if Z.leb (bv_unsigned (copy_dst c)) (bv_unsigned a)
       && Z.ltb (bv_unsigned a)
                 (bv_unsigned (copy_dst c) + bv_unsigned (copy_len c))
    then before (Z_to_bv 64
           (bv_unsigned (copy_src c)
            + (bv_unsigned a - bv_unsigned (copy_dst c))))
    else mem a.

Fixpoint apply_copies (before mem : word -> option byte) (cs : list MemCopy)
    : word -> option byte :=
  match cs with
  | [] => mem
  | c :: r => apply_copies before (apply_copy before mem c) r
  end.

(** Apply a chosen effect: set a0 (= x10) to the return value, snapshot the
    pre-effect memory, erase the unmapped ranges, zero-fill the granted
    ranges, copy preserved bytes from the snapshot, and write exactly the
    declared byte ranges.  SP, every other GPR, the LR/SC reservation,
    ROM, and all memory outside the declared ranges are preserved BY
    CONSTRUCTION — the generative spec cannot silently rewrite anything
    it did not declare, so no frame side-conditions are needed.
    (Mechanically, writes land in the writable overlay [ms_mem] at
    whatever addresses the effect declares; the SPECS guarantee those
    addresses are writable-mapped — output buffers are checked against
    [in_wmem], the copy_to_user/EFAULT analogue, zero ranges are fresh
    anonymous grants, mremap growth tails, noaccess pages made rw, or a
    live rw range replaced by MAP_FIXED or zapped by
    madvise(MADV_DONTNEED), and unmap ranges are tracked anonymous
    subranges.  A moved-growing mremap
    deliberately combines all three symbolic ledgers; the ordering above
    preserves its old prefix.  A brk transition either grows (zeros, no
    unmaps) or shrinks (unmaps, no zeros).) *)
Definition apply_effect (ms : machine_state) (eff : SyscallEffect)
    : machine_state :=
  let ms' := set_reg ms 10 (eff_ret eff) in
  {| ms_regs := ms_regs ms'; ms_fregs := ms_fregs ms';
     ms_pc_val := ms_pc_val ms';
     ms_svc_pending := ms_svc_pending ms';
     ms_resv := ms_resv ms'; ms_fcsr := ms_fcsr ms';
     ms_mem := apply_writes
                 (apply_copies (ms_mem ms')
                   (apply_zeros (apply_unmaps (ms_mem ms') (eff_unmaps eff))
                                (eff_zeros eff))
                   (eff_copies eff))
                 (eff_writes eff);
     ms_rom := ms_rom ms' |}.

(** Advance PC past the ecall instruction (+4), clear svc_pending, and
    CLEAR THE LR/SC RESERVATION.

    Linux breaks the reservation on every return to user mode.
    [ret_from_exception] (arch/riscv/kernel/entry.S, Linux v6.18.46,
    commit 1f99e9ab748f) ends with

        REG_L  a2, PT_EPC(sp)
        REG_SC x0, a2, PT_EPC(sp)

    above the comment "so instead here we clear any existing reservation
    -- it's always legal for implementations to clear load reservations
    at any point".  An [ecall] from user mode enters [handle_exception],
    which dispatches [do_trap_ecall_u] and then jumps to
    [ret_from_exception], so that [REG_SC] runs on the syscall return
    too.  The unprivileged specification (the A extension, LR/SC) makes
    that enough: "An SC must fail if there is another SC (to any
    address) between the LR and the SC in program order".  So after
    [lr.w a0,(s0); ecall; sc.w a1,a2,(s0)] the [sc] fails on Linux,
    whatever the memory holds.

    QEMU user mode answers otherwise: its syscall path
    ([RISCV_EXCP_U_ECALL] in [cpu_loop], linux-user/riscv/cpu_loop.c,
    QEMU 10.0.11) never writes [env->load_res], and the only
    [load_res = -1] outside CPU reset and [gen_sc] is in
    [riscv_cpu_set_mode] (target/riscv/cpu_helper.c), which
    [CONFIG_USER_ONLY] builds out.  So the [sc] of that sequence can
    succeed under qemu-user.  LPS describes Linux v6.18.46, so it
    answers Linux's; SCOPE.md's list "Where QEMU user mode differs"
    carries the difference. *)
Definition advance_past_svc (ms : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms;
     ms_pc_val := ms_pc ms + Z_to_bv 64 4;
     ms_svc_pending := None;
     ms_resv := None; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms;
     ms_rom := ms_rom ms |}.

(* =========================================================================
   Configurations and the one-step relation
   ========================================================================= *)

Record config := mkCfg {
  cfg_ms    : machine_state;
  cfg_model : Model;
}.

(** The address space the kernel already used at [execve]: each LOAD
    segment, PAGE-ROUNDED.  Segments are [N]-based snapshot data far
    below 2^64, so the rounding in [Z] re-enters [word] losslessly. *)
Definition segment_reservation (s : Segment) : word * word :=
  let lo := page_round_down_Z (Z.of_N (seg_base s)) in
  let hi := page_round_up_Z (Z.of_N (seg_base s) + Z.of_N (seg_size s)) in
  (Z_to_bv 64 lo, Z_to_bv 64 (hi - lo)).

Definition segments_reserved (segs : list Segment) : list (word * word) :=
  map segment_reservation segs.

(** Where a step can go: on to another configuration, or the explicit
    error transition. *)
Inductive step_to :=
  | SNext (c : config)
  | SError.

Section WithMemImage.

Variable mi_loaded_segments : list Segment.
Variable mi_init_pc : N.        (* [N]-based snapshot datum (MemImage) *)

(** Where the binary's program header table landed ([MemImageType.PhdrInfo]):
    [N]-based snapshot data like [mi_init_pc], published to the process
    through AT_PHDR/AT_PHENT/AT_PHNUM in the initial stack's auxiliary
    vector ([StackLayout.auxv_entries]).  It is what lets a static libc
    find PT_TLS and lay out thread-local storage; see [PhdrInfo]. *)
Variable mi_phdrs : PhdrInfo.

Variable mi_init_sp : word.

(** The initial program break, chosen NON-DETERMINISTICALLY at [execve]
    (brk ASLR), exactly like [mi_init_sp]: any [valid_brk] value —
    page-aligned, from the page-rounded image top up to [brk_aslr_max]
    above it — quantified INDEPENDENTLY for the two binaries in
    [Equivalence.strong_universal_T].  It is not snapshot data, and a
    target may not assume the source's break placement.  Seeds
    [State.init_model]'s [vm_brk]; [Mmap.brk_spec]'s query path
    (brk(0)) reports it, as [sbrk(0)] observes on Linux. *)
Variable mi_init_brk : word.

(** The run's [mm->mmap_base], chosen NON-DETERMINISTICALLY at [execve]
    exactly like [mi_init_sp] and [mi_init_brk]: any [valid_mmap_base]
    value — page-aligned, within [State.mmap_base_min ..
    State.mmap_base_max] — quantified INDEPENDENTLY for the two binaries
    in [Equivalence.strong_universal_T].  On Linux the value is a
    function of the stack rlimit, [stack_guard_gap], the layout
    personality and sysctls, [vm.mmap_rnd_bits] and the mmap ASLR draw
    ([arch_pick_mmap_layout], mm/util.c:465-479, Linux v6.18.46, commit
    1f99e9ab748f — the derivation is on [State.mmap_base_min] and the cap
    on [State.mmap_base_max]); none of that is snapshot data, so the
    model quantifies over the band instead.  The band is exactly the set
    of bases Linux gives under the assumptions SCOPE.md names
    ([Checks.Cases.MmapBase.sv48_band_is_linux_set]).
    Seeds [State.init_model]'s [vm_mmap_base].  THE SPEC READS THAT
    VALUE: both fresh-grant arms of [Mmap.mmap_spec], and [mremap]'s
    move, choose their address with [Mmap.linux_place], whose top-down
    half searches below [State.mmap_top], which is the minimum of this
    base and [State.alloc_top] (see [Mmap.mmap_spec]'s PLACEMENT
    section).  The untrusted search in
    theories/Common/PlacementSearch.v takes its floor as a bare argument
    rather than off a [VmMaps].  The ASan plan checker's placement gate
    ([Common.AsanCeil.placement_ok]) reads it too; that gate is the
    theorem [Common.AsanCeil.placement_policy_holds], proved from
    [Mmap.linux_place], and no longer a hypothesis the checker names.
    The PREDICATE over the value
    is what [valid_entry] carries — see [valid_mmap_base]. *)
Variable mi_mmap_base : word.

(** The 16 bytes of startup entropy AT_RANDOM points at, drawn afresh at
    [execve] exactly like [mi_init_sp], [mi_init_brk] and
    [mi_mmap_base]: [create_elf_tables] (fs/binfmt_elf.c, Linux
    v6.18.46, commit 1f99e9ab748f) calls
    [get_random_bytes(k_rand_bytes, sizeof(k_rand_bytes))] and copies the
    result onto the new stack for AT_RANDOM to point at.  Carried as a
    [bv 128] and serialized by [StackLayout.at_random_bytes]; unlike the
    three placements it has NO validity predicate, because every 128-bit
    value is a draw the kernel can make.  Quantified INDEPENDENTLY for
    the two binaries in [Equivalence.strong_universal_T], which is what
    makes a program whose output depends on its startup entropy
    unprovable against anything — the same treatment, for the same
    reason, as a program that leaks its stack address.  It is read by
    exactly one thing, the last 16 bytes of
    [StackLayout.build_stack_bytes]; no address in the layout moves with
    it ([StackLayout.build_stack_bytes_split_random]).

    Carried inside [StackLayout.EntryDraw] together with [ed_slack], the
    bytes of the entry stack's last page ABOVE that block: the two are
    the byte-level things [execve] settles that this model does not
    determine, and both are read only through [entry_stack_image] below.
    See that record for the kernel side of each and for why neither is
    zeros. *)
Variable mi_draw : EntryDraw.

(** The run's backed anonymous-memory budget in bytes ([State.vm_limit]):
    [State.vm_backing_used] may never rise above it, so the out-of-memory
    point of an unboundedly-allocating program is forced — by a fixed
    budget, not by a quantified draw.  It is NOT determined
    by the grant-and-free history alone: overlapping [vm_maps] entries
    make the total depend on placement too (see [State.live_bytes]), and
    [Equivalence.equiv] compares trace SETS, so the target must
    reproduce every point the source can reach.

    A PARAMETER of the semantics rather than a baked-in constant so
    a caller can choose a small budget (exhaustion is then
    cheap to reach);
    [Equivalence.strong_equiv] pins it per role to
    [State.source_alloc_limit]/[State.target_alloc_limit]. *)
Variable mi_alloc_limit : Z.

Let mi_step := RiscvSemantics.step mi_loaded_segments.
Let mi_step_accesses := RiscvSemantics.step_accesses mi_loaded_segments.

(** Execute one instruction and atomically charge every newly touched page in
    a lazy anonymous reservation.  The interpreter returns the complete access
    report before this function changes the model, so an instruction spanning
    two new pages either charges both or takes the fault transition. *)
Definition mi_account_step (ms : machine_state) (model : Model)
    : machine_result (machine_state * Model) :=
  match mi_step_accesses ms with
  | MachineOk report =>
      match materialize_model_accesses model (@accessed_ranges _ report) with
      | Some model' => MachineOk (@access_value _ report, model')
      | None => MachineFault
      end
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.

(** Accounting is an overlay on the authoritative instruction semantics: a
    successful accounted step has exactly the machine state produced by
    [RiscvSemantics.step]. *)
Lemma mi_account_step_projects : forall ms model ms' model',
  mi_account_step ms model = MachineOk (ms', model') ->
  mi_step ms = MachineOk ms'.
Proof.
  intros ms model ms' model' Haccount.
  unfold mi_account_step, mi_step_accesses in Haccount.
  remember (RiscvSemantics.step_accesses mi_loaded_segments ms) as stepped
    eqn:Hstepped.
  destruct stepped as [report| |]; [|discriminate|discriminate].
  destruct (materialize_model_accesses model (@accessed_ranges _ report))
    as [accounted|] eqn:Hmaterialized; [|discriminate].
  inversion Haccount; subst.
  pose proof (RiscvSemantics.drop_step_accesses mi_loaded_segments ms) as Hdrop.
  rewrite <- Hstepped in Hdrop. cbn in Hdrop. symmetry. exact Hdrop.
Qed.

Lemma mi_account_step_model_frame : forall ms model ms' model',
  mi_account_step ms model = MachineOk (ms', model') ->
  m_fd model' = m_fd model /\
  m_vmmaps model' = m_vmmaps model /\
  m_vm_lazy model' = m_vm_lazy model /\
  m_io model' = m_io model /\
  m_fsys model' = m_fsys model /\
  m_proc model' = m_proc model /\
  m_lim model' = m_lim model.
Proof.
  intros ms model ms' model' Haccount.
  unfold mi_account_step, mi_step_accesses in Haccount.
  destruct (RiscvSemantics.step_accesses mi_loaded_segments ms)
    as [report| |] eqn:Hstepped; [|discriminate|discriminate].
  destruct (materialize_model_accesses model (@accessed_ranges _ report))
    as [accounted|] eqn:Hmaterialized; [|discriminate].
  inversion Haccount; subst.
  exact (materialize_model_accesses_frame model
           (@accessed_ranges _ report) model' Hmaterialized).
Qed.

(** With no lazy mappings there is nothing to charge, so accounting erases
    completely and preserves the model as well as the machine step. *)
Lemma mi_account_step_no_lazy : forall ms model,
  m_vm_lazy model = [] ->
  mi_account_step ms model =
    match mi_step ms with
    | MachineOk ms' => MachineOk (ms', model)
    | MachineFault => MachineFault
    | MachineUnmodeled => MachineUnmodeled
    end.
Proof.
  intros ms model Hlazy.
  unfold mi_account_step, mi_step_accesses, mi_step.
  remember (RiscvSemantics.step_accesses mi_loaded_segments ms) as stepped
    eqn:Hstepped.
  pose proof (RiscvSemantics.drop_step_accesses mi_loaded_segments ms) as Hdrop.
  rewrite <- Hstepped in Hdrop.
  rewrite <- Hdrop.
  destruct stepped as [[ms' accesses]| |]; cbn; try reflexivity.
  rewrite (materialize_model_accesses_no_lazy model accesses Hlazy).
  reflexivity.
Qed.

(** The input handed to the syscall spec: the syscall number, the
    argument registers, the COMPLETE pre-syscall memory ([ms_read_byte])
    and the WRITABLE view ([ms_writable_byte]). *)
Definition sys_input (ms : machine_state) (x8 : word) : SyscallInput :=
  mkInput x8 (syscall_args ms) (ms_read_byte ms)
          (ms_writable_byte mi_loaded_segments ms).

(** One transition. *)
Inductive sstep : config -> list event -> step_to -> Prop :=
| sstep_instr : forall ms model ms' model',
    m_halted model = None ->
    ms_svc_pending ms = None ->
    mi_account_step ms model = MachineOk (ms', model') ->
    sstep (mkCfg ms model) [] (SNext (mkCfg ms' model'))
| sstep_instr_fault : forall ms model,
    m_halted model = None ->
    ms_svc_pending ms = None ->
    mi_account_step ms model = MachineFault ->
    sstep (mkCfg ms model) [] SError
| sstep_instr_unmodeled : forall ms model,
    m_halted model = None ->
    ms_svc_pending ms = None ->
    mi_account_step ms model = MachineUnmodeled ->
    sstep (mkCfg ms model) [] SError
| sstep_syscall : forall ms model x8 eff model' model'' evs,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    syscall_spec (sys_input ms x8) model (Ok eff model' evs) ->
    m_halted model' = None ->
    materialize_model_accesses model' (syscall_effect_accesses eff)
      = Some model'' ->
    sstep (mkCfg ms model) evs
          (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
| sstep_syscall_materialization_fault : forall ms model x8 eff model' evs,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    syscall_spec (sys_input ms x8) model (Ok eff model' evs) ->
    m_halted model' = None ->
    materialize_model_accesses model' (syscall_effect_accesses eff) = None ->
    sstep (mkCfg ms model) [] SError
| sstep_exit : forall ms model x8 eff model' evs code,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    syscall_spec (sys_input ms x8) model (Ok eff model' evs) ->
    m_halted model' = Some code ->
    m_killed model' = None ->
    sstep (mkCfg ms model) (evs ++ [ExitEv code (m_fs model')])
          (SNext (mkCfg ms model'))
(** The other way a process ends: a fatal signal it sent itself.  Same
    shape as [sstep_exit] and the same discarded effect -- the syscall
    completes in the kernel and the process is killed on the way back to
    user space, so what it wrote to its own memory is never read -- and
    the two arms are disjoint by [m_killed], which [sstep_exit]
    requires to be [None].

    THE DECLARATION IS NOT A PREMISE HERE.  For SIGABRT it is one
    inside [Kernel.Signal.tkill_spec]; for SIGPIPE there is none at
    all, because [Sys.Fs.ReadWrite.write_spec]'s three write arms raise
    it from ordinary modeled state.  Putting a declaration here as well
    would make this rule unable to fire on an outcome the spec layer
    produced -- which is a STUCK configuration, not a decline, and
    [sstep_cfg_progress] below would be false.  What carries the
    abort-compatibility claim instead is [decl_off_frame] above, stated
    once and consumed by [sstep_off_no_kill], and it is a claim about
    SIGABRT alone. *)
| sstep_killed : forall ms model x8 eff model' evs sig,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    syscall_spec (sys_input ms x8) model (Ok eff model' evs) ->
    m_killed model' = Some sig ->
    sstep (mkCfg ms model) (evs ++ [KillEv sig (m_fs model')])
          (SNext (mkCfg ms model'))
| sstep_syscall_unmodeled : forall ms model x8,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    syscall_spec (sys_input ms x8) model Unmodeled ->
    sstep (mkCfg ms model) [] SError.

(** Kleene star of [sstep], accumulating events. *)
Inductive star : config -> list event -> config -> Prop :=
| star_refl : forall c, star c [] c
| star_step : forall c1 evs c2 tr c3,
    sstep c1 evs (SNext c2) ->
    star c2 tr c3 ->
    star c1 (evs ++ tr) c3.

Lemma star_one : forall c evs c',
  sstep c evs (SNext c') -> star c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs).
  econstructor; eauto using star_refl.
Qed.

Lemma star_trans : forall c1 t1 c2 t2 c3,
  star c1 t1 c2 -> star c2 t2 c3 -> star c1 (t1 ++ t2) c3.
Proof.
  intros c1 t1 c2 t2 c3 H1; revert t2 c3.
  induction H1; intros t2 c3' H2; cbn; [assumption|].
  rewrite <- app_assoc. econstructor; eauto.
Qed.

(* =========================================================================
   Observable behavior: finite trace prefixes + reachability of error
   ========================================================================= *)

(** [tr] is an event-level prefix of an admissible run (prefix-closed at
    BYTE granularity). *)
Definition obs_trace (c0 : config) (tr : list event) : Prop :=
  exists tr' c, star c0 tr' c /\ is_prefix tr tr'.

Lemma obs_trace_nil : forall c0, obs_trace c0 [].
Proof.
  intros c0. exists [], c0. split; [apply star_refl | apply is_prefix_nil].
Qed.

Lemma obs_trace_prefix_closed : forall c0 tr tr',
  obs_trace c0 tr -> is_prefix tr' tr -> obs_trace c0 tr'.
Proof.
  intros c0 tr tr' (tr'' & c & Hstar & Hp) Hp'.
  exists tr'', c. eauto using is_prefix_trans.
Qed.

(* =========================================================================
   The declaration off adds no behavior: what that rests on
   ========================================================================= *)

(** THE FRAME THE COMPATIBILITY CLAIM RESTS ON, NAMED RATHER THAN
    ASSUMED SILENTLY.

    [State.in_abort_terminal] is meant to be inert when it is [false]: a
    run whose task did not declare the abort path should produce exactly
    the traces, errors and uncovered points it would produce if 130 and
    131 had no arms.  Two of the three things that has to mean are facts
    about the SPEC LAYER rather than about this file — that no syscall
    arm turns the declaration on, that none records a SIGABRT kill under
    it, and that none emits a [State.KillEv] of its own — and this
    development has no lemma quantified over the arms of
    [Sys.SyscallTable.spec_table] to prove them with.  The arms are not
    counted here on purpose: a number in prose is the part that goes
    stale, which is the rule [Checks.Cases.Kernel.Signal]'s
    [sig_mask_windows] header states and the reason it names its
    syscalls instead.

    IT IS ABOUT SIGABRT AND NOT ABOUT KILLS.  [State.with_killed] has a
    second signal, SIGPIPE, raised by the three write arms of
    [Sys.Fs.ReadWrite.write_spec] from ordinary modeled state, and NOTHING
    gates those on a declaration — a pipe whose read end the program
    closed is state the program made, not a stance a task took.  So "no
    kill with the declaration off" is FALSE, and the frame says what is
    true instead: no kill CARRYING SIGABRT.  A reader who wants the
    stronger reading will not find it here, and [sstep_off_no_kill] says
    in as many words what it no longer rules out.

    So they are a hypothesis with a name.  [decl_off_frame] states
    exactly what the abort path's code establishes BY
    INSPECTION: [State.with_abort_terminal] has one caller
    ([State.init_model]); [State.with_killed]'s SIGABRT callers are two,
    [Kernel.Signal.send_sigabrt] and [Kernel.Signal.sigmask_deliver_model]'s
    SIGABRT branch;
    and no spec emits any event but [State.ReadEv] and [State.WriteEv].
    Every other setter carries the three fields across, which is what the
    [m_killed_with_*], [m_sigabrt_pending_with_*] and
    [m_abort_terminal_with_*] blocks in
    theories/LinuxProcessSem/State.v say, one [reflexivity] each.

    IT IS AN INVARIANT AND NOT A ONE-SIDED FRAME, and the second
    hypothesis is the whole reason.  Of those two callers only the first
    is behind [State.m_abort_terminal]:
    [Kernel.Signal.sigmask_deliver_model] branches on
    [State.m_sigabrt_pending] instead, because a signal already pending
    has to be delivered by the mask install that uncovers it whatever
    the task declared.  So the declaration ALONE does not keep a kill
    out — a model with the declaration clear and the pending bit set is
    directly constructible, and an ordinary
    [rt_sigprocmask(SIG_UNBLOCK, {SIGABRT})] kills it.
    [Checks.Cases.Kernel.Signal.decl_off_frame_one_sided_refuted] is
    that model, and it refutes the one-sided form.

    What IS true is the pair moving together: with both bits clear no
    arm can set either, because the only writer of the pending bit is
    [Kernel.Signal.send_sigabrt], which IS behind the declaration.  That
    is why the hypothesis carries [m_sigabrt_pending] and the conclusion
    re-establishes it, and why [State.init_model] — which clears both —
    is the base case the run-level consequence starts from.

    This is the same standing [State.with_children]'s note describes for
    [procst_children]: a property maintained by every construction site
    and documented at the setter, which a new setter can break without
    breaking any proof.  Writing it as a hypothesis is one step better
    than that note — the consequences below are mechanized, and the day
    a table-wide frame lemma exists it is discharged rather than
    assumed. *)
(** The signal the abort path sends, as the word a [State.KillEv] and
    [State.m_killed] carry.  Named here because the frame below and its
    two lemmas are claims about THIS SIGNAL and not about kills in
    general; see the paragraph above them. *)
Definition sigabrt_word : word := Z_to_bv 64 SIGABRT.

Definition decl_off_frame : Prop :=
  forall i m eff m' evs,
    syscall_spec i m (Ok eff m' evs) ->
    m_abort_terminal m = false ->
    m_sigabrt_pending m = false ->
    m_abort_terminal m' = false
    /\ m_sigabrt_pending m' = false
    /\ m_killed m' <> Some sigabrt_word
    /\ (forall sig fs, ~ In (KillEv sig fs) evs).

(** The form this had before, kept ONLY so that
    [Checks.Cases.Kernel.Signal.decl_off_frame_one_sided_refuted] has
    something to refute.  Nothing may consume it: it is FALSE, and a
    theorem stated with it as a hypothesis is vacuous.  It is the shape
    a reader reaches for first — the declaration is the switch, so surely
    the declaration is the guard — and the refutation is what says why
    that reading is wrong. *)
Definition decl_off_frame_one_sided : Prop :=
  forall i m eff m' evs,
    syscall_spec i m (Ok eff m' evs) ->
    m_abort_terminal m = false ->
    m_abort_terminal m' = false
    /\ m_killed m' = None
    /\ (forall sig fs, ~ In (KillEv sig fs) evs).

Lemma m_abort_terminal_proc : forall m1 m2,
  m_proc m1 = m_proc m2 -> m_abort_terminal m1 = m_abort_terminal m2.
Proof. intros m1 m2 H. unfold m_abort_terminal. now rewrite H. Qed.

Lemma m_sigabrt_pending_proc : forall m1 m2,
  m_proc m1 = m_proc m2 -> m_sigabrt_pending m1 = m_sigabrt_pending m2.
Proof. intros m1 m2 H. unfold m_sigabrt_pending. now rewrite H. Qed.

(** One step, with the declaration off and nothing pending: BOTH bits
    stay clear, and the events the step contributes carry no SIGABRT
    kill.  The pending bit is carried for the reason the frame carries
    it — see [decl_off_frame] — and dropping it from either side makes
    this lemma's hypothesis the false one.

    WHAT IT NO LONGER RULES OUT, said once so that nobody reads "no
    kill" where this says "no SIGABRT kill": a step MAY contribute a
    [State.KillEv] carrying SIGPIPE (13) with both abort bits clear and
    the declaration off, because the three write arms of
    [Sys.Fs.ReadWrite.write_spec] raise that signal from ordinary
    modeled state — a pipe whose read end the program closed, a socket
    with no connection, a channel the launch says has no reader — and
    none of those is behind the abort declaration.  This lemma is about
    the abort path's inertness and about nothing else. *)
Lemma sstep_off_no_kill : decl_off_frame ->
  forall ms model evs c',
    m_abort_terminal model = false ->
    m_sigabrt_pending model = false ->
    sstep (mkCfg ms model) evs (SNext c') ->
    m_abort_terminal (cfg_model c') = false
    /\ m_sigabrt_pending (cfg_model c') = false
    /\ (forall fs, ~ In (KillEv sigabrt_word fs) evs).
Proof.
  intros Hframe ms model evs c' Hoff Hpend Hstep.
  inversion Hstep; subst.
  - (* instruction: accounting keeps [State.m_proc] fixed *)
    match goal with
    | [ H : mi_account_step _ _ = MachineOk (_, _) |- _ ] =>
        destruct (mi_account_step_model_frame _ _ _ _ H) as (_&_&_&_&_&Hp&_)
    end.
    cbn [cfg_model]. split; [| split; [| intros fs []]].
    + rewrite <- Hoff. apply m_abort_terminal_proc. exact Hp.
    + rewrite <- Hpend. apply m_sigabrt_pending_proc. exact Hp.
  - (* a syscall that materializes: the frame, then materialization,
       which keeps [State.m_proc] fixed too *)
    match goal with
    | [ Hs : syscall_spec _ _ (Ok _ ?m1 _),
        Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ ] =>
        destruct (Hframe _ _ _ _ _ Hs Hoff Hpend) as (Hoff' & Hpend' & _ & Hev);
        destruct (materialize_model_accesses_frame _ _ _ Hm) as (_&_&_&_&_&Hp&_)
    end.
    cbn [cfg_model].
    split; [| split; [| intros fs Hin; exact (Hev _ _ Hin)]].
    + rewrite <- Hoff'. apply m_abort_terminal_proc. exact Hp.
    + rewrite <- Hpend'. apply m_sigabrt_pending_proc. exact Hp.
  - (* exit: the effect is discarded, so the post-model is the spec's *)
    match goal with
    | [ Hs : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
        destruct (Hframe _ _ _ _ _ Hs Hoff Hpend) as (Hoff' & Hpend' & _ & Hev)
    end.
    split; [exact Hoff' | split; [exact Hpend' |]].
    intros fs Hin. apply in_app_or in Hin.
    destruct Hin as [Hin | [Hin | []]]; [exact (Hev _ _ Hin) | discriminate].
  - (* kill: the frame says no arm records a SIGABRT kill from a state
       with both bits clear, so the appended event carries some OTHER
       signal, and the two bits come across unchanged *)
    match goal with
    | [ Hs : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
        destruct (Hframe _ _ _ _ _ Hs Hoff Hpend) as (Hoff' & Hpend' & Hk & Hev)
    end.
    split; [exact Hoff' | split; [exact Hpend' |]].
    intros fs Hin. apply in_app_or in Hin.
    destruct Hin as [Hin | [Hin | []]]; [exact (Hev _ _ Hin) |].
    apply Hk. injection Hin as Hsig Hfs. congruence.
Qed.

(** In a whole execution, the same.  [State.init_model] clears both bits
    ([State.m_sigabrt_pending_init_model], and
    [State.m_abort_terminal_init_model] reads the declaration off the
    input), so a run whose task did not declare the abort path meets
    this lemma's hypotheses at its first configuration.  It says NO
    SIGABRT KILL and not "no kill"; see [sstep_off_no_kill]. *)
Lemma star_off_no_kill : decl_off_frame ->
  forall c tr c',
    m_abort_terminal (cfg_model c) = false ->
    m_sigabrt_pending (cfg_model c) = false ->
    star c tr c' ->
    forall fs, ~ In (KillEv sigabrt_word fs) tr.
Proof.
  intros Hframe c tr c' Hoff Hpend Hstar.
  revert Hoff Hpend.
  induction Hstar as [c | c1 evs c2 tr c3 Hstep Hstar IH];
    intros Hoff Hpend; [intros fs []|].
  destruct c1 as [ms model]. cbn [cfg_model] in Hoff, Hpend.
  destruct (sstep_off_no_kill Hframe _ _ _ _ Hoff Hpend Hstep)
    as (Hoff' & Hpend' & Hev).
  intros fs Hin. apply in_app_or in Hin.
  destruct Hin as [Hin | Hin];
    [ exact (Hev fs Hin) | exact (IH Hoff' Hpend' fs Hin) ].
Qed.

Lemma in_is_prefix {A} : forall (x : A) l1 l2,
  is_prefix l1 l2 -> In x l1 -> In x l2.
Proof.
  intros x l1; induction l1 as [|a l1 IH]; intros [|b l2] Hp Hin;
    cbn in *; try contradiction.
  destruct Hp as (-> & Hp). destruct Hin as [-> | Hin]; [now left|].
  right. exact (IH l2 Hp Hin).
Qed.

(** The run can take the explicit error transition. *)
Definition reaches_error (c0 : config) : Prop :=
  exists tr c evs, star c0 tr c /\ sstep c evs SError.

(* =========================================================================
   Coverage: where the MODEL gives up, as opposed to where the PROGRAM dies
   ========================================================================= *)

(** [c] is a configuration this model does not cover.  There are exactly
    two ways to be uncovered, matching the two places the semantics can
    decline to say what happens:

    - the pending instruction is [MachineUnmodeled] — a word the decoder
      does not decode, an instruction outside the modeled subset, or an
      unmodeled ISA boundary node (see [RiscvSemantics.machine_result]);
    - the pending syscall's spec yields [Unmodeled] — the fail-closed arm of
      [Specs.syscall_spec], reached by a syscall number outside
      [Specs.modeled_sysnos], by unmodeled flags, or by a buffer the
      spec declines to interpret ([Monad.unmodeled] means "the model does
      not cover this", never "Linux would fail here": real Linux
      failures are modeled as [Ok] with a negative errno).

    Deliberately NOT included: [MachineFault] (a wild jump, an unmapped
    load, a store into a read-only segment, an [ebreak]).  Those are
    faithful models of a process that really does die, and a source
    binary is entitled to reach them.  This is the whole point of the
    distinction — an equivalence task is allowed to be about a program
    that crashes, but it must not be about a program the semantics
    failed to follow.

    THAT EXCLUSION IS A CLAIM ABOUT SIGNAL DISPOSITIONS, and it is not
    self-evident: a process that has installed a SIGSEGV handler does
    NOT die here, it runs the handler and carries on.  So the exclusion
    holds only while no fault signal can have a handler, which is why
    [Signal.sigaction_accepted] refuses an [rt_sigaction] install for
    SIGSEGV, SIGBUS, SIGILL and SIGTRAP, and why no modeled syscall can
    SEND one of the four.  [Specs.modeled_sysnos] contains no [kill]
    (129) and no [rt_sigreturn] (139); it does contain [tkill] (130) and
    [tgkill] (131), and what stands in for their absence is
    [Kernel.Signal.tkill_self]'s envelope, which sends SIGABRT and
    declines every other signal — so no fault signal is reachable
    through them either, and a widening there is a widening HERE.
    Widening any of those without also routing [MachineFault] to
    [unmodeled_at] makes
    this premise false, and the cost is not a wrong answer but a silent
    one: every execution reaches [SError], [Equivalence.bh_all_errors]
    holds, [Equivalence.equiv]'s escape admits an ARBITRARY target, and
    [Equivalence.modeled] is still satisfied because a fault is not
    unmodeled.  The theorem stays true and says nothing.

    BLOCKING A FAULT SIGNAL DOES NOT WEAKEN THAT EXCLUSION, which is
    worth saying because a mask can be set: [force_sig_info_to_task]
    (kernel/signal.c) resets the disposition to SIG_DFL and removes the
    signal from the mask before delivering a synchronous fault, so a
    process that blocks SIGSEGV and then faults dies exactly as one
    that never blocked it.

    THE SIGNALS THE ACCEPTED SET LETS THROUGH REST ON A SECOND PREMISE,
    WHICH IS THIS DEVELOPMENT'S AND NOT LINUX'S: THE ENVIRONMENT THIS
    THEOREM QUANTIFIES OVER DELIVERS NO SIGNALS AT ALL.
    [State.ProcInput] quantifies argv, envp, the file system and stdin
    and quantifies no signal source; [sstep] has no transition a signal
    could arrive on; [State.Model] holds no disposition, mask or pending
    queue.  So an [rt_sigaction] install that [Signal.sigaction_accepted]
    admits stores nothing (it charges only the 24-byte copy-in of
    [act]), and the SIGINT and SIGTERM it admits are
    exactly the signals that an OUTSIDE sender — not any modeled
    operation — could raise.  Two binaries that differ only in
    whether they installed such a handler have identical traces here
    (wherever that copy-in's charge does not decide the budget) and
    differ under a real signal, so the premise is what makes their
    equivalence true rather than merely provable.  It is a premise,
    stated nowhere as a hypothesis because there is no state for it to
    constrain.  Applying this theorem to a program
    whose environment does send signals is outside what it was proved
    about.

    THAT PREMISE HAS A SECOND HALF, AND IT IS THE ONE WITH TEETH:
    THE PROCESS STARTS WITH SIGABRT AT ITS DEFAULT DISPOSITION.
    [Kernel.Signal.tkill_self] is a modeled operation that
    DELIVERS a signal rather than merely admitting an install, so
    "the model holds no disposition" is not harmless.  The disposition a modeled operation could install is
    covered — [Signal.rt_sigaction_spec] answers an install for signal 6
    only with the handler SIG_DFL, the disposition it already assumes
    ([Checks.Cases.Kernel.Signal.rt_sigaction_sigabrt_dfl_accepted]), and
    declines SIG_IGN and a handler address
    ([Checks.Cases.Kernel.Signal.rt_sigaction_sigabrt_ign_unmodeled],
    [Checks.Cases.Kernel.Signal.rt_sigaction_sigabrt_handler_unmodeled]) —
    but the disposition the process INHERITS is not: [begin_new_exec]
    calls [flush_signal_handlers(me, 0)], and that function resets a
    slot only [if (force_default || ka->sa.sa_handler != SIG_IGN)], so
    SIG_IGN survives execve where a handler does not (kernel/signal.c
    and fs/exec.c, Linux v6.18.46, commit 1f99e9ab748f; execve(2) says
    the same).  A launcher that ignores SIGABRT and then execs the
    binary hands this model a process it kills and Linux does not —
    [get_signal]'s [if (ka->sa.sa_handler == SIG_IGN) continue] — which
    is an ACCEPTANCE of a trace Linux cannot produce rather than a
    refusal of one it can, the direction the design priorities (README.md) call a bug.

    IT IS A PREMISE ABOUT THE LAUNCH, in the same position as
    [Kernel.Exit.wait4_spec]'s empty child and tracee lists, and nothing
    here checks it: a launcher that does not leave SIGABRT at SIG_DFL
    is outside the model.  The premise is only reachable at all under
    [valid_input_abort]: with the declaration clear, [tkill_self]
    declines and no disposition can matter.

    [Kernel.Signal.rt_sigprocmask_spec] (135) rests on the same premise
    and leans on it hardest, being the only modeled syscall that both
    changes how a signal would be handled and REPORTS the answer back to
    the program.  It keeps the mask in [State.ProcState] and copies the
    entry value out through [oset], so what the premise costs here is
    not coverage but a VALUE: Linux has two writers of [->blocked] that
    no program calls — [signal_delivered] (kernel/signal.c), which
    unions in [sa_mask] on handler entry, and riscv's
    [SYSCALL_DEFINE0(rt_sigreturn)] (arch/riscv/kernel/signal.c), which
    restores it from the sigframe — and neither has an arm here.  Under
    a delivered signal the eight bytes this spec hands back would be the
    wrong number, where a spec that merely declined would have been
    incomplete instead.  Two binaries differing only in what they block
    are not equivalent under this theorem, but the answer is right only
    while nothing is delivered.  The reasoning is in
    [Sys/Kernel/Signal.v]'s header.

    THE SIGPIPE DISPOSITION IS NOT ON THIS LIST ANY MORE: IT IS A
    DECLARED FIELD.  [Sys.Fs.ReadWrite.write_spec] is a modeled
    operation that DELIVERS signal 13 -- on a write to a pipe with no
    reader (fs/pipe.c [anon_pipe_write] :460-465), to a socket with no
    connection (net/core/stream.c [sk_stream_error] :190-198), and to a
    channel the launch declares unread ([State.in_channel_reader]) --
    so the inherited disposition decides the OUTCOME of those calls and
    not merely a returned number.

    Nothing a modeled run does can move it:
    [Kernel.Signal.rt_sigaction_spec] declines EVERY install for signal
    13 ([Kernel.Signal.sigaction_accepted] admits 2 and 15, and
    [Kernel.Signal.sigabrt_dfl_install] admits only signal 6).  What
    the LAUNCH did is the live question, by the same
    [flush_signal_handlers] argument: SIG_IGN survives execve, and
    `signal(SIGPIPE, SIG_IGN)` before exec is COMMON -- commoner than
    ignoring SIGABRT.  Left as a premise it would be an unstated one
    with teeth: a launcher that ignores SIGPIPE hands the model a
    process it kills where Linux returns -EPIPE and continues, an
    ACCEPTANCE of a trace Linux cannot produce.

    SO IT IS [State.in_sigpipe_default], and [valid_input] pins it to
    [true].  A statement quantified over [valid_input] now SAYS which
    world it is about rather than assuming one, and the other world has
    its own predicate, [valid_input_sigpipe_ignored], under which
    [Sys.Fs.ReadWrite.raise_sigpipe] discards the signal and no write
    arm can end the run.  The alternative considered and rejected was
    declining every write once the launch could have ignored the
    signal, which gives back exactly the coverage this revision bought.
    BLOCKING is a third, independent matter and was already modeled: a
    launch whose [in_sigmask] blocks signal 13 is a valid input, the
    write answers -EPIPE, and [State.procst_sigpipe_pending] carries
    the signal to the [rt_sigprocmask] that uncovers it. *)
Definition unmodeled_at (c : config) : Prop :=
  m_halted (cfg_model c) = None /\
  ( (ms_svc_pending (cfg_ms c) = None /\
       mi_account_step (cfg_ms c) (cfg_model c) = MachineUnmodeled)
    \/ (exists x8, ms_svc_pending (cfg_ms c) = Some x8 /\
                   syscall_spec (sys_input (cfg_ms c) x8) (cfg_model c) Unmodeled) ).

(** The run can reach a configuration the model does not cover. *)
Definition reaches_unmodeled (c0 : config) : Prop :=
  exists tr c, star c0 tr c /\ unmodeled_at c.

(** Being uncovered is a special case of erroring: both uncovered shapes
    are premises of an [SError] transition.  Consequently every proof of
    [~ reaches_error] — which the simulation library already produces for
    the well-behaved paths — discharges [~ reaches_unmodeled] for free,
    and only the paths that genuinely fault need new reasoning. *)
Lemma unmodeled_at_sstep_error : forall c,
  unmodeled_at c -> exists evs, sstep c evs SError.
Proof.
  intros [ms model] (Hh & [(Hsvc & Hstep) | (x8 & Hsvc & Hspec)]); cbn in *.
  - exists []. apply sstep_instr_unmodeled; assumption.
  - exists []. eapply sstep_syscall_unmodeled; eassumption.
Qed.

Lemma reaches_unmodeled_reaches_error : forall c0,
  reaches_unmodeled c0 -> reaches_error c0.
Proof.
  intros c0 (tr & c & Hstar & Hun).
  destruct (unmodeled_at_sstep_error c Hun) as (evs & Hss).
  exists tr, c, evs. split; assumption.
Qed.

Lemma no_error_no_unmodeled : forall c0,
  ~ reaches_error c0 -> ~ reaches_unmodeled c0.
Proof. intros c0 H Hun. apply H, reaches_unmodeled_reaches_error, Hun. Qed.

(** NON-VACUITY.  Everything above is a way of RULING OUT
    [reaches_unmodeled], so it is worth pinning that the predicate is
    inhabited — otherwise [Equivalence.modeled] would be a clause no
    binary could ever violate, and adding it to the obligation would buy
    nothing.  Every machine state the step function declines is a
    witness, reached in zero steps.  (For a CONCRETE inhabitant, closed
    under no hypotheses at all, see
    [Checks.Examples.run_of_undecodable_image_is_unmodeled] and
    [Checks.Examples.run_of_undecodable_image_refutes_modeled], and for
    the fetch-side shape [Checks.RiscvCompressedFetch.badhex_step_unmodeled].
    Compare
    [all_traces_error_reaches_error], which guards the other quantifier
    the same way: a guard nobody can trip is a guard that guards
    nothing.) *)
Lemma reaches_unmodeled_intro : forall ms model,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step ms model = MachineUnmodeled ->
  reaches_unmodeled (mkCfg ms model).
Proof.
  intros ms model Hh Hsvc Hstep.
  exists [], (mkCfg ms model). split; [apply star_refl|].
  split; [exact Hh|]. left. split; assumption.
Qed.

(** Every maximal execution from [c0] reaches the explicit error
    transition after finitely many steps.

    This is the accessibility predicate for the relation formed by
    [SNext] transitions, with an additional progress premise.  The
    progress premise prevents halted or stuck configurations from
    satisfying the predicate vacuously.  The recursive premise covers
    EVERY [SNext] successor, so one chosen erroring resolution cannot
    hide a different successor that exits or diverges without error.

    Being inductive is important: a configuration with an infinite
    [SNext] execution cannot construct this proof merely because an
    error alternative remains available at every finite prefix. *)
Inductive all_traces_error : config -> Prop :=
| all_traces_error_intro : forall c,
    (exists evs to, sstep c evs to) ->
    (forall evs c', sstep c evs (SNext c') -> all_traces_error c') ->
    all_traces_error c.

(** Universal error implies existential error.  Keeping this lemma next
    to the definitions makes the intended relationship between the two
    behavior fields explicit and guards against an accidentally vacuous
    universal predicate. *)
Lemma all_traces_error_reaches_error : forall c,
  all_traces_error c -> reaches_error c.
Proof.
  intros c Hall. induction Hall as [c Hprogress Hnext IH].
  destruct Hprogress as (evs & to & Hstep). destruct to as [c' |].
  - destruct (IH evs c' Hstep) as (tr & c2 & err_evs & Hstar & Herr).
    exists (evs ++ tr), c2, err_evs. split; [|exact Herr].
    econstructor; eauto.
  - exists [], c, evs. split; [apply star_refl | exact Hstep].
Qed.

(** ** Initial machine state at [execve]

    Sets PC (from the [N]-based snapshot); SP (x2) is the quantified
    [mi_init_sp].  Populates stack memory with Linux's entry block
    (StackLayout.v) from [mi_init_sp] up to the stack VMA's end
    [StackLayout.ed_top]; the dynamic stack region below SP is
    zero-mapped.  All other registers start at 0; no LR/SC reservation
    is held.

    [State.in_uid] and [State.in_gid] are the fields
    [State.init_model] copies into the credentials the id syscalls
    read, so the auxv on the stack and [getuid]'s answer come from ONE
    source and cannot disagree — as they cannot on Linux, where
    [create_elf_tables] and [SYSCALL_DEFINE0(getuid)] both munge
    [current_cred()->uid] (Linux v6.18.46, commit 1f99e9ab748f,
    fs/binfmt_elf.c and kernel/sys.c). *)

(** ** What the launch, rather than the image or the caller, puts in
       the auxv

    [StackLayout.LaunchAuxv] from the run's [State.KernelBuild], the
    entry's mmap base and the declared address-space size.

    AT_SYSINFO_EHDR is [base - T]: [__setup_additional_pages]
    (arch/riscv/kernel/vdso.c, Linux v6.18.46, commit 1f99e9ab748f)
    maps the vvar pages and then the text with [get_unmapped_area],
    which under the top-down layout returns the highest free range
    below [mm->mmap_base].  At that moment only the image's segments
    and the stack exist, so the pair lands directly below the base and
    the text's start is [base - vdso_text_pages * 4096]. *)
Definition launch_cache_words (kb : KernelBuild) : CacheWords :=
  let w := fun l => Z_to_bv 64 (cache_size_word l) in
  let g := fun l => Z_to_bv 64 (cache_geometry_word l) in
  let c := kb_cache kb in
  mkCacheWords (w (cv_l1i c)) (g (cv_l1i c))
               (w (cv_l1d c)) (g (cv_l1d c))
               (w (cv_l2 c))  (g (cv_l2 c))
               (w (cv_l3 c))  (g (cv_l3 c)).

Definition vdso_text_base (kb : KernelBuild) (mbase : word) : word :=
  Z_to_bv 64 (bv_unsigned mbase - vdso_text_pages kb * page_size).

Definition launch_auxv (inp : ProcInput) (mbase : word) : LaunchAuxv :=
  let kb := in_kernel inp in
  mkLaunchAuxv (vdso_text_base kb mbase)
               (launch_cache_words kb)
               (Z_to_bv 64 (min_sigframe_size kb (in_hwcap inp)))
               (kb_rseq kb).

(** ** The entry stack image

    THE BLOCK IS THE WHOLE IMAGE.  [StackLayout.build_stack_bytes] now
    runs from [sp] to the stack VMA's end [StackLayout.ed_top], which
    [setup_arg_pages] (fs/exec.c, Linux v6.18.46, commit 1f99e9ab748f)
    page-aligns, so there is no page tail above it and nothing for the
    entry to choose there.  [ed_slack] and [entry_slack] are gone with
    it: the model used to lay a block SHORTER than the kernel's and
    draw the bytes above it, because it published no exec file name and
    only ten auxv entries.

    [entry_page_top] is [ed_top]. *)
Definition entry_block_top (sp : word) (bytes : list byte) : Z :=
  (bv_unsigned sp + Z.of_nat (length bytes))%Z.

Definition entry_page_top (draw : EntryDraw) : Z :=
  bv_unsigned (ed_top draw).

Definition entry_stack_image (inp : ProcInput) (mbase : word)
    (ph : PhdrInfo) (entry sp : word) (draw : EntryDraw) : list byte :=
  build_stack_bytes (launch_auxv inp mbase) ph entry sp (ed_top draw)
    (in_argv inp) (in_envp inp) (in_execfn inp)
    (in_uid inp) (in_gid inp) (in_hwcap inp) draw.

(** ** The stack window: RLIMIT_STACK counts the entry image, and the
       guard gap above the vDSO stops it

    Below the entry image, [init_machine_state] zero-maps the stack
    that the program can grow into.  Two things bound it, and Linux
    applies both in [expand_downwards] (mm/vma.c, Linux v6.18.46):

    - RLIMIT_STACK.  [expand_downwards] passes
      [size = vma->vm_end - address] to [acct_stack_growth], which
      refuses the growth when [size > rlimit(RLIMIT_STACK)].  So the 8
      MiB ([State.stack_max_size]) is counted from [vm_end], which is
      [ed_top], not from [sp] and not from the top of the block.
    - THE GUARD GAP.  [expand_downwards] refuses to grow within
      [stack_guard_gap] of the mapping below.  At entry that mapping is
      the vDSO text, directly below the mmap base, so the floor is
      [base + guard gap].

    The floor is the higher of the two, and it is below [sp] for every
    launch the fifth conjunct of [valid_entry_va] admits: with
    randomization the base and its gap are at most
    [STACK_TOP - 0x407ff000] while [ed_top] is at least
    [STACK_TOP - 2^30], and without it the base and its gap are at most
    [STACK_TOP - 8 MiB] while [ed_top] is at least [STACK_TOP - 4096].

    An earlier version zero-mapped [[sp - stack_max_size, sp)], which
    counted 8 MiB from [sp]
    (theorem-labs/rocq-linux-process-semantics#6), and the version
    before this one counted it from the top of the block and had no
    guard-gap floor at all (#25). *)
Definition stack_window_lo (kb : KernelBuild) (mbase : word)
    (draw : EntryDraw) : Z :=
  Z.max (bv_unsigned (ed_top draw) - stack_max_size)
        (bv_unsigned mbase + stack_guard_gap_bytes kb).

Definition init_machine_state (inp : ProcInput) : machine_state :=
  let regs :=
    bvmap_set 2 mi_init_sp                 (* sp *)
      (bvmap_set 10 (Z_to_bv 64 0)         (* a0 — 0 on Linux entry; the entry is
                                              redundant (missing keys read as 0)
                                              but register-file proofs match on
                                              the map shape, so keep it *)
         bvmap_empty) in                   (* every other register reads as 0 *)
  (* execve zeroes the FP state: an empty FP register file (missing
     keys read as 0) and fcsr = 0, i.e. no accrued exceptions and
     round-to-nearest-even as the dynamic mode. *)
  {| ms_regs := regs; ms_fregs := bvmap_empty;
     ms_pc_val := Z_to_bv 64 (Z.of_N mi_init_pc);
     ms_svc_pending := None;
     ms_resv := None; ms_fcsr := Z_to_bv 32 0;
     ms_mem :=
       let img := entry_stack_image inp mi_mmap_base mi_phdrs
                    (Z_to_bv 64 (Z.of_N mi_init_pc)) mi_init_sp mi_draw in
       let stk := stack_to_mem mi_init_sp img in
       fun addr =>
         match stk addr with
         | Some b => Some b
         | None =>
           if andb (Z.leb (stack_window_lo (in_kernel inp) mi_mmap_base mi_draw)
                          (bv_unsigned addr))
                   (Z.ltb (bv_unsigned addr) (bv_unsigned mi_init_sp))
           then Some (Z_to_bv 8 0)
           else None
         end;
     ms_rom := fun addr =>
       match memory_read mi_loaded_segments addr 1 with
       | Some (b :: _) => Some b
       | _ => None
       end |}.

(** The initial configuration for one run of THIS image on the
    caller-supplied inputs [inp]. *)
Definition init_config (inp : ProcInput) : config :=
  mkCfg (init_machine_state inp)
        (init_model (segments_reserved mi_loaded_segments) mi_init_brk
                    mi_mmap_base mi_init_sp mi_alloc_limit inp).

End WithMemImage.

Global Strategy 100 [init_machine_state].

(* =========================================================================
   Running a binary: the three groups of arguments
   ========================================================================= *)

(** What [execve] chooses for THIS run, as opposed to what the binary or
    the caller supplies: the initial stack pointer, the program break
    and the mmap base — all placed non-deterministically (ASLR and the
    layout draw: [valid_sp], [valid_brk], [valid_mmap_base]) — and
    [StackLayout.EntryDraw], the two byte-level choices in the entry
    stack image the model does not determine: the 16 bytes of startup
    entropy AT_RANDOM points at ([get_random_bytes] in
    [create_elf_tables], fs/binfmt_elf.c, Linux v6.18.46, commit
    1f99e9ab748f; see [mi_draw] above and
    [StackLayout.at_random_bytes]), and the bytes of the entry stack's
    last page above the block ([entry_slack]).  All four fields are
    quantified independently per binary in
    [Equivalence.strong_universal_T].

    Three of the four have a window and appear in [valid_entry]; the
    draw has none, because every value of either of its halves is one a
    kernel can produce.  That asymmetry is the whole of what the field
    costs a consumer: a statement quantifying over entries covers more
    dimensions and gains no hypothesis to discharge.

    The two draws are ONE field rather than two because they are one
    thing: the bytes of the initial stack image that the kernel settles
    and this model does not.  Splitting them would put a second
    unconstrained field beside the first and change no statement.

    The register file needs no field:
    on Linux entry every register but sp is 0 (argc/argv live on the
    stack), so [init_machine_state] pins them architecturally. *)
Record ExecEntry := mkEntry {
  en_sp        : word;
  en_brk       : word;
  en_mmap_base : word;
  en_draw      : EntryDraw
}.

(** Everything observable about one binary on one input.  The record
    arguments are the three sources the run draws on: the ELF-derived
    image ([MemImageType.Image]), the values [execve] picked for this
    process ([ExecEntry]), and the caller-supplied inputs
    ([State.ProcInput], declared next to [State.init_model], the first
    function that consumes it, and validated by [valid_input] below);
    [lim] is the environment's backed anonymous-memory budget
    ([mi_alloc_limit] — a bare capacity in bytes, not a record: it is
    neither image data, nor an [execve] choice, nor caller input, and
    [Equivalence.strong_equiv] pins it per role).

    Written as a MATCH on the image and the [execve] entry, so that a
    proof unfolding it with [cbn [run …]] gets the underlying
    [init_config] application back as soon as those two arguments are
    concrete records — the projections would otherwise have to be named
    in every such [cbn]; [valid_entry] below is written the same way.
    The [ProcInput] is passed whole and read by projections, which
    reduce, so [cbn [run …]] reaches [init_config] for a variable [inp]
    too. *)
Definition run (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput)
    : behavior :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    let c0 := init_config segs pc ph sp brk0 mbase rnd lim inp in
    {| bh_traces := obs_trace segs c0;
       bh_errors := reaches_error segs c0;
       bh_all_errors := all_traces_error segs c0;
       bh_unmodeled := reaches_unmodeled segs c0 |}
  end.

(* =========================================================================
   Spurious environment failures, per family: [SpuriousCfg] and [run_scfg]
   =========================================================================

   ** What is being parameterised

   Some syscall arms answer an errno the model cannot DERIVE from its
   state: [openat] of a file that exists may still fail with -ENOMEM or
   -EACCES, [dup] with -EMFILE, [mmap] with -ENOMEM while budget remains,
   [getrandom] with -EINTR.  Each such arm draws from a per-syscall list
   with [Syscall.errno_from] under an [alt] beside the answer the state
   does determine, so that the failure stays LIVE — a target that deleted
   the source's error handling would otherwise remain equivalent.  Under
   every statement above this section that is the only reading: the
   environment may refuse at any such call.

   That reading makes two things unprovable that a task may want.  An
   error-free statement about a program whose out-of-memory path aborts,
   when its allocations never come near the budget; and any
   [Classifier.decides] statement about a classifier that reads its
   input file, because a run on which the open is refused reaches
   neither verdict.  So a task chooses, per FAMILY of
   injected failure, between two readings:

     - MAY FAIL: the default reading, the one every statement above has;
     - FAILS ONLY IF FORCED: the arm's errno is admitted only where the
       model's state leaves no other answer.

   [SpuriousCfg] is that choice, one boolean per family, [true] meaning
   "may fail".  [may_fail_cfg] is the reading every existing statement
   keeps ([run_scfg_may_fail] below), [forced_only_cfg] is the other
   extreme, and [alloc_only_cfg b] is the one-switch form for the
   allocation family.  The
   configuration is a parameter of a STATEMENT, fixed by the sealed
   module type a checker ascribes ([Equivalence.SPEC_SCFG]); it is not a
   field of the model and not a quantified draw, so nothing under
   [Sys/] and nothing in [State] changes.

   ** The six families, and where "forced" comes from

   The table below ([injected_table]) lists every arm that injects, by
   syscall number, with its family and the list it draws from — the
   very lists the specs use, so the two cannot drift.  What "forced"
   means per family is not written anywhere as a state test; it is READ
   OFF THE SPEC by the definition of [spurious_refusal_cfg], and this is
   what each family's forcing condition comes to:

     alloc  mmap, brk, mremap, mprotect,  the shape's budget test fails,
            munmap                        or no placement exists;
                                          munmap: never
     fs     openat, faccessat,            openat: no free descriptor;
            faccessat2, unlinkat,         the others: never
            getcwd, getdents64, write     (write's is the page an empty
                                          pipe's write must allocate)
     fd     dup, pipe2, socket,           no free descriptor (two for
            socketpair, accept, clone     pipe2 and socketpair; accept
                                          also when [Socket.conn_ix_exhausted]);
                                          clone: never
     net    bind, listen                  never
     cred   setuid, setgid, setresuid,    never; setsid's -EPERM after a
            setresgid, setsid             success is deterministic and
                                          keyed on [State.m_setsid_succeeded]
     intr   getrandom, nanosleep          never (the model delivers no
                                          signals)

   A family whose refusal is never forced simply loses the errno under
   forced-only.  [brk] is the one arm that refuses by VALUE rather than
   by errno — a grow or shrink that answers the OLD break — so its
   entry carries no errno list and [brk_refusal_b] names the refusal.

   ** How the filter is stated, and why it is exact

   [spurious_refusal_cfg cfg i m eff] holds when the syscall's family is
   forced-only in [cfg], [eff] is one of that syscall's refusals, AND the
   spec admits at [(i, m)] some outcome that is NOT one — a success, or
   an errno the state determines.  A refusal is removed only where it
   was avoidable.

   So the filter is exact BY CONSTRUCTION rather than by mirroring each
   arm's branch structure.  An errno the state forces — the budget is
   spent, the descriptor table is full, [setsid] already succeeded — is
   the only answer at its state, so no non-refusal outcome exists there
   and it is kept.  An answer the state DETERMINES is never removed:
   if the spec admits it beside an injected errno at one state, then by
   the spec's own construction it is the answer the injection stands
   beside, and it is not a refusal.  A wrong or over-inclusive errno
   list can therefore only lose filtering; it can never remove an answer
   Linux is forced to give.  What the design pays for that is the third
   conjunct being an existential over spec outcomes rather than a
   boolean; see the KNOWN GAP below.

   ** The filtered run is a subset of [run]

   [sstep_cfg cfg] is [sstep] with one extra premise on the two
   constructors that consume a syscall outcome: the outcome is not a
   spurious refusal.  So every filtered step is a step
   ([sstep_cfg_sub]), every filtered trace, error and uncovered point is
   one of the run's ([obs_trace_cfg_sub], [reaches_error_cfg_sub],
   [reaches_unmodeled_cfg_sub]), and at [may_fail_cfg] the premise is
   vacuous and the two relations coincide ([sstep_cfg_may_fail],
   [run_scfg_may_fail]).  Forced-only REMOVES executions and adds none.
   It is also monotone in the configuration ([sstep_cfg_mono]): turning
   a family off removes steps and never adds one.

   ** KNOWN GAP: the executable checker certifies the may-fail reading

   [Checks.ExecutableSpecs] decides membership of ONE outcome in the
   spec, and [Checks.Progress] exhibits ONE admissible outcome per
   input — for [mmap] and [openat], the errno.  Neither answers the
   question the forced-only filter asks: whether a NON-REFUSAL outcome
   exists at [(i, m)].  For most families that is a descriptor-table
   test, but for [mmap] and [mremap] it is a placement question — is
   there a free page-aligned range below [State.alloc_top] — and
   nothing in the trusted tree computes one.  [refusal_decided] below
   names exactly that question; [sstep_cfg_progress] shows the filtered
   run never gets stuck where it is answered, so a computable placement
   witness is what would close the gap for the allocation family.  Until
   then a proof made under forced-only answers the placement question itself,
   at the calls it reasons about, exactly as the simulation library
   already exhibits placements for the success path. *)

(** The six families of injected environment failure. *)
Inductive SpuriousFamily :=
  | FamAlloc | FamFs | FamFd | FamNet | FamCred | FamIntr.

(** One boolean per family: [true] = "always allowed to fail" (the
    reading every statement above this section has), [false] = "fails
    only if forced".  A record rather than a function so the generated
    checker can spell a configuration as a literal. *)
Record SpuriousCfg := mkSpuriousCfg {
  sc_alloc : bool;
  sc_fs    : bool;
  sc_fd    : bool;
  sc_net   : bool;
  sc_cred  : bool;
  sc_intr  : bool
}.

Definition may_fail_cfg : SpuriousCfg := mkSpuriousCfg true true true true true true.
Definition forced_only_cfg : SpuriousCfg := mkSpuriousCfg false false false false false false.

(** The one-switch form: the allocation family alone, every
    other family left at may-fail. *)
Definition alloc_only_cfg (alloc_may_fail : bool) : SpuriousCfg :=
  mkSpuriousCfg alloc_may_fail true true true true true.

Definition family_may_fail (cfg : SpuriousCfg) (f : SpuriousFamily) : bool :=
  match f with
  | FamAlloc => sc_alloc cfg
  | FamFs    => sc_fs cfg
  | FamFd    => sc_fd cfg
  | FamNet   => sc_net cfg
  | FamCred  => sc_cred cfg
  | FamIntr  => sc_intr cfg
  end.

(** [cfg1] admits no family [cfg2] does not: the pointwise order on the
    six booleans.  [forced_only_cfg] is its least element and
    [may_fail_cfg] its greatest. *)
Definition cfg_le (cfg1 cfg2 : SpuriousCfg) : Prop :=
  forall f, family_may_fail cfg1 f = true -> family_may_fail cfg2 f = true.

Lemma cfg_le_refl : forall cfg, cfg_le cfg cfg.
Proof. intros cfg f H. exact H. Qed.

Lemma forced_only_cfg_least : forall cfg, cfg_le forced_only_cfg cfg.
Proof. intros cfg f H. destruct f; discriminate H. Qed.

Lemma may_fail_cfg_greatest : forall cfg, cfg_le cfg may_fail_cfg.
Proof. intros cfg f _. destruct f; reflexivity. Qed.

(** One injecting arm: the syscall number, its family, and the errnos its
    [Syscall.errno_from] draws from — the spec's own list, named rather
    than copied. *)
Record InjectedArm := mkInjectedArm {
  ia_no     : Z;
  ia_family : SpuriousFamily;
  ia_errnos : list Z
}.

(** Every arm of [Sys.SyscallTable.spec_table] that injects, SORTED BY
    SYSCALL NUMBER like that table and for the same reason (two changes
    that add two arms land at different lines).  [brk] refuses by value
    and carries no list; see [brk_refusal_b].  [nanosleep]'s -EINTR,
    [setsid]'s -EPERM and [write]'s -ENOMEM on a pipe's fresh page are
    injected by a bare [alt] rather than through a named list, so their
    lists are written here.  [faccessat2] draws from
    [faccessat]'s list because both answer through
    [Fs.Open.access_exists_spec].

    NANOSLEEP LISTS -EINTR AND NOT -EFAULT, AND THAT ASYMMETRY IS A
    DECISION rather than an oversight — it is written here because the
    next reader will otherwise close it in the wrong direction.  Since
    the remainder pointer took its range test
    ([Sys.Kernel.Time.Hrtimer.nanosleep_spec]), an [rmtp] that
    [State.access_okb] refuses answers -EFAULT, and that answer is
    reachable ONLY through an interruption: a completed sleep never
    copies the remainder out.  So -EINTR and -EFAULT come from the same
    injection, and only one of them is in the list.
    LISTING AN ERRNO MAKES [forced_only_cfg] FILTER THE OUTCOME, so
    adding -EFAULT here would stop a proof having to handle a case a
    real run produces — an interrupted sleep whose remainder pointer is
    out of range.  Leaving it unlisted keeps that outcome and costs a
    proof one case it can discharge.  The cheap error is the one that
    keeps the case, so the list stays as it is.
    What would have to be true for the other choice: that no covered
    program can present an out-of-range [rmtp] to an interrupted sleep
    — which is a fact about the programs, not about this table, and
    nothing in this tree states it.
    A refused [rqtp] is not affected either way: its -EFAULT is the
    only outcome at that state, so it is kept under both readings. *)
Definition injected_table : list InjectedArm :=
  (* getcwd     *) mkInjectedArm  17%Z FamFs    getcwd_errnos ::
  (* dup        *) mkInjectedArm  23%Z FamFd    dup_errnos ::
  (* unlinkat   *) mkInjectedArm  35%Z FamFs    unlinkat_errnos ::
  (* faccessat  *) mkInjectedArm  48%Z FamFs    faccessat_errnos ::
  (* openat     *) mkInjectedArm  56%Z FamFs    openat_errnos ::
  (* pipe2      *) mkInjectedArm  59%Z FamFd    pipe2_errnos ::
  (* getdents64 *) mkInjectedArm  61%Z FamFs    getdents64_errnos ::
  (* write      *) mkInjectedArm  64%Z FamFs    write_errnos ::
  (* nanosleep  *) mkInjectedArm 101%Z FamIntr  [EINTR] ::
  (* setgid     *) mkInjectedArm 144%Z FamCred  (setid_errnos true) ::
  (* setuid     *) mkInjectedArm 146%Z FamCred  (setid_errnos true) ::
  (* setresuid  *) mkInjectedArm 147%Z FamCred  (setid_errnos true) ::
  (* setresgid  *) mkInjectedArm 149%Z FamCred  (setid_errnos true) ::
  (* setsid     *) mkInjectedArm 157%Z FamCred  [EPERM] ::
  (* socket     *) mkInjectedArm 198%Z FamFd    socket_errnos ::
  (* socketpair *) mkInjectedArm 199%Z FamFd    (socketpair_reserve_errnos ++ socketpair_create_errnos) ::
  (* bind       *) mkInjectedArm 200%Z FamNet   bind_errnos ::
  (* listen     *) mkInjectedArm 201%Z FamNet   listen_errnos ::
  (* accept     *) mkInjectedArm 202%Z FamFd    accept_errnos ::
  (* brk        *) mkInjectedArm 214%Z FamAlloc [] ::
  (* munmap     *) mkInjectedArm 215%Z FamAlloc munmap_errnos ::
  (* mremap     *) mkInjectedArm 216%Z FamAlloc mremap_errnos ::
  (* clone      *) mkInjectedArm 220%Z FamFd    clone_errnos ::
  (* mmap       *) mkInjectedArm 222%Z FamAlloc mmap_errnos ::
  (* mprotect   *) mkInjectedArm 226%Z FamAlloc mprotect_errnos ::
  (* accept4    *) mkInjectedArm 242%Z FamFd    accept_errnos ::
  (* getrandom  *) mkInjectedArm 278%Z FamIntr  getrandom_errnos ::
  (* clone3     *) mkInjectedArm 435%Z FamFd    clone_errnos ::
  (* faccessat2 *) mkInjectedArm 439%Z FamFs    faccessat_errnos ::
  nil.

Fixpoint lookup_injected (t : list InjectedArm) (n : Z) : option InjectedArm :=
  match t with
  | [] => None
  | a :: r => if Z.eqb (ia_no a) n then Some a else lookup_injected r n
  end.

(** The injecting arm for a syscall number, keyed exactly as
    [Sys.Dispatch.dispatch] keys the spec table. *)
Definition injected_arm (no : Z) : option InjectedArm :=
  lookup_injected injected_table no.

(** [r] is one of the errno returns in [es]. *)
Definition ret_in_errnos (es : list Z) (r : word) : bool :=
  existsb (fun e => bv_eqb r (errno_ret e)) es.

(** [brk req] answered [ret] from the pre-step model [m]: a refusal iff
    [req] is a real request (neither the query nor an address below
    [Mmap.min_brk], both of which the state answers with the old break),
    asks to MOVE the break, and the answer is the old break unmoved.
    Mirrors the three paths of [Mmap.brk_r_ok]. *)
Definition brk_refusal_b (m : Model) (req ret : word) : bool :=
  let h := m_vmmaps m in
  let b := vm_brk h in
  negb (w_is0 req)
  && negb (Z.ltb (bv_unsigned req) (bv_unsigned (min_brk h)))
  && negb (bv_eqb req b)
  && bv_eqb ret b.

(** Is the answer [ret] to the syscall [i] at model [m] one of its
    injected refusals?  For every arm but [brk], one of the listed
    errnos; for [brk], the old break on a request to move it.  A syscall
    with no injecting arm has no refusals. *)
Definition refusal_b (i : SyscallInput) (m : Model) (ret : word) : bool :=
  let no := bv_unsigned (in_sysno i) in
  if Z.eqb no 214 then brk_refusal_b m (in_arg i 0) ret
  else match injected_arm no with
       | Some a => ret_in_errnos (ia_errnos a) ret
       | None => false
       end.

(** Is the pending syscall [i] at model [m] a grant the BUDGET refuses?
    Every [FamAlloc] arm of [injected_table], each answered by the mark
    its own file defines beside its spec
    ([Mmap.brk_budget_refused_b], [Mmap.munmap_budget_refused_b],
    [Mremap.mremap_budget_refused_b], [Mmap.mmap_budget_refused_b],
    [Mprotect.mprotect_budget_refused_b])
    on the arguments [Sys.SyscallTable.spec_table] hands the arm; every
    other number is [false].  [munmap]'s mark is [false] too, on every
    request: munmap consults no budget, and its one refusal is never a
    budget one ([alloc_budget_refused_munmap]).  Compare [refusal_b],
    which asks whether a given ANSWER is a refusal; this asks whether the
    REQUEST is one the budget declines, whatever answer is then drawn.

    THE [false] IS THE DANGEROUS ANSWER: an allocation arm this
    dispatcher does not know is a silent false negative of the budget
    premise.  Two pins keep the enumeration complete.
    [alloc_family_dispatched] proves that every number
    [injected_table] registers under [FamAlloc] is in
    [alloc_mark_sysnos], and [alloc_budget_refused_b_outside] that the
    dispatcher answers [false] exactly off that list, so a sixth
    [FamAlloc] arm fails to build until the list and the dispatcher
    learn it.  What Rocq cannot see is an arm that consults the budget
    without registering as injecting, so that rule is stated here
    instead: every file under [Sys/] that names a
    budget reader must define a [*_budget_refused_b] this dispatcher
    names. *)
Definition alloc_mark_sysnos : list Z := [214; 215; 216; 222; 226]%Z.

Definition alloc_budget_refused_b (i : SyscallInput) (m : Model) : bool :=
  let no := bv_unsigned (in_sysno i) in
  if Z.eqb no 214 then brk_budget_refused_b m (in_arg i 0)
  else if Z.eqb no 215 then munmap_budget_refused_b (in_arg i 0) (in_arg i 1) m
  else if Z.eqb no 216 then
    mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m
  else if Z.eqb no 222 then
    mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
      (in_arg i 4) (in_arg i 5) m
  else if Z.eqb no 226 then
    mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) m
  else false.

(** ** Classifying a budget refusal: oversize vs cumulative

    [alloc_budget_refused_b] records that a request was refused for
    budget, not why.  [alloc_refuse_reason] reads the same pre-state and
    request and gives [RefuseOversize] when the request's charge alone
    exceeds [State.vm_limit], and [RefuseBudget] otherwise.  It adds no
    transition; each arm still answers its own refusal (-ENOMEM, or the
    unmoved break for [brk]).  The threshold is the budget, not a
    per-request cap.

    A premise built on [budget_only_refused_at] still excludes: a
    cumulative refusal of a request that fits the budget alone, whatever
    controls its size; every first-touch refusal of a MAP_NORESERVE
    mapping; and a [brk] whose growth fits the budget but whose heap does
    not (the charge is the growth above the current break). *)
Inductive RefuseReason : Set := RefuseBudget | RefuseOversize.

(** The charge of the pending request: the PAGES a [brk] grow installs
    above the current break ([Sys/Mm/Mmap.brk_grow_bytes], the same
    range the ledger records and the gate charges), the page-rounded
    length or new size for
    [mremap], [mmap] and [mprotect], and 0 for any other syscall —
    [munmap] included, whose mark never fires.  The argument indices are
    those of [alloc_budget_refused_b]; the per-arm lemmas below tie this
    charge to each arm's gate. *)
Definition alloc_req_charge_bytes (i : SyscallInput) (m : Model) : Z :=
  let no := bv_unsigned (in_sysno i) in
  if Z.eqb no 214 then brk_grow_bytes (m_vmmaps m) (in_arg i 0)
  else if Z.eqb no 216 then page_round_up_Z (bv_unsigned (in_arg i 2))
  else if Z.eqb no 222 then page_round_up_Z (bv_unsigned (in_arg i 1))
  else if Z.eqb no 226 then page_round_up_Z (bv_unsigned (in_arg i 1))
  else 0%Z.

(** The classified budget refusal.  [None] exactly when the request is
    not budget-refused at all; otherwise the cause.  [RefuseOversize]
    takes priority: a refused request whose charge alone exceeds the whole
    budget is classified oversize, however much budget is left. *)
Definition alloc_refuse_reason (i : SyscallInput) (m : Model)
    : option RefuseReason :=
  if alloc_budget_refused_b i m
  then if Z.ltb (vm_limit (m_vmmaps m)) (alloc_req_charge_bytes i m)
       then Some RefuseOversize   (* the request alone exceeds the budget *)
       else Some RefuseBudget     (* refused only by cumulative use *)
  else None.

(** Faithfulness: the classifier refines [alloc_budget_refused_b] and
    changes nothing — it fires on exactly the configurations the mark
    already fires on, so no new input is excluded or admitted. *)
Lemma alloc_refuse_reason_none_iff_not_refused : forall i m,
  alloc_refuse_reason i m = None <-> alloc_budget_refused_b i m = false.
Proof.
  intros i m. unfold alloc_refuse_reason.
  destruct (alloc_budget_refused_b i m).
  - destruct (Z.ltb (vm_limit (m_vmmaps m)) (alloc_req_charge_bytes i m));
      split; intro H; discriminate.
  - split; intros; reflexivity.
Qed.

(** *** The charge is the refusing gate's own charge, arm by arm

    For each [FamAlloc] arm: where its mark fires, the budget gate the
    arm consults is false when applied to [alloc_req_charge_bytes].  For
    [brk] the gate is [vm_backing_used + charge <= vm_limit] verbatim;
    for the other arms the charge is the page-rounded size [n] each
    gate is applied to. *)
Lemma alloc_req_charge_brk : forall i m,
  bv_unsigned (in_sysno i) = 214%Z ->
  alloc_budget_refused_b i m = true ->
  (0 <= alloc_req_charge_bytes i m)%Z
  /\ brk_budget_ok m (in_arg i 0)
     = (vm_backing_used m + alloc_req_charge_bytes i m <=? vm_limit (m_vmmaps m))%Z
  /\ brk_budget_ok m (in_arg i 0) = false.
Proof.
  intros i m Hno Hb.
  unfold alloc_budget_refused_b in Hb. cbv zeta in Hb. rewrite Hno in Hb.
  cbn [Z.eqb Pos.eqb] in Hb.
  unfold brk_budget_refused_b in Hb.
  apply andb_true_iff in Hb as [Hb Hok].
  apply negb_true_iff in Hok.
  assert (Hc : alloc_req_charge_bytes i m
               = brk_grow_bytes (m_vmmaps m) (in_arg i 0)).
  { unfold alloc_req_charge_bytes. cbv zeta. rewrite Hno.
    cbn [Z.eqb Pos.eqb]. reflexivity. }
  split; [rewrite Hc; unfold brk_grow_bytes; lia |]. split; [| exact Hok].
  unfold brk_budget_ok. cbv zeta. rewrite Hc. reflexivity.
Qed.

(** THE MREMAP MARK, READ BACK.  The grow has ONE non-errno
    resolution, and which one is decided by the room test
    ([Sys/Mm/Mremap.mremap_inplace_room_b]), so the mark says a
    different thing in each case: with room, the in-place charge
    fails; without room, the move's charge fails.  What holds in BOTH
    is that the in-place resolution is not admitted.

    Before the placement change this lemma could claim both halves at
    once, because the mark was [negb (inplace_grow || move_budget)].
    It cannot now, and it should not: Linux with room above the source
    does not move, so the move's budget says nothing about that
    call (mm/mremap.c, [vrm_can_expand_in_place] and the accounting
    failure beside it, Linux v6.18.46, commit 1f99e9ab748f). *)
Lemma alloc_req_charge_mremap : forall i m,
  bv_unsigned (in_sysno i) = 216%Z ->
  alloc_budget_refused_b i m = true ->
  let old_nZ := page_round_up_Z (bv_unsigned (in_arg i 1)) in
  let c := alloc_req_charge_bytes i m in
  (old_nZ < c)%Z
  /\ mremap_inplace_grow_b m (in_arg i 0) (Z_to_bv 64 old_nZ) (Z_to_bv 64 c) old_nZ c = false
  /\ (if mremap_inplace_room_b m (in_arg i 0) (Z_to_bv 64 old_nZ) (Z_to_bv 64 c) old_nZ c
      then mremap_final_budget_b m (in_arg i 0) (Z_to_bv 64 old_nZ)
             (in_arg i 0) (Z_to_bv 64 c) = false
      else mremap_move_budget_b m (in_arg i 0) (Z_to_bv 64 old_nZ)
             (Z_to_bv 64 c) = false).
Proof.
  intros i m Hno Hb old_nZ c.
  assert (Hc : c = page_round_up_Z (bv_unsigned (in_arg i 2))).
  { subst c. unfold alloc_req_charge_bytes. cbv zeta. rewrite Hno. reflexivity. }
  rewrite Hc. subst old_nZ.
  unfold alloc_budget_refused_b in Hb. cbv zeta in Hb. rewrite Hno in Hb.
  cbn [Z.eqb Pos.eqb] in Hb.
  unfold mremap_budget_refused_b in Hb. cbv zeta in Hb.
  repeat match type of Hb with
         | context [if ?b then _ else _] => destruct b eqn:?; try discriminate Hb
         end;
  match goal with
  | [ H : (page_round_up_Z (bv_unsigned (in_arg i 2))
           <=? page_round_up_Z (bv_unsigned (in_arg i 1)))%Z = false |- _ ] =>
      apply Z.leb_gt in H
  end;
  apply negb_true_iff in Hb;
  (split; [assumption|]);
  unfold mremap_inplace_grow_b;
  match goal with
  | [ Hr : mremap_inplace_room_b _ _ _ _ _ _ = true |- _ ] =>
      rewrite Hr; cbn [andb]; split; [exact Hb | exact Hb]
  | [ Hr : mremap_inplace_room_b _ _ _ _ _ _ = false |- _ ] =>
      rewrite Hr; cbn [andb]; split; [reflexivity | exact Hb]
  end.
Qed.

Lemma alloc_req_charge_mmap : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  alloc_budget_refused_b i m = true ->
  let c := alloc_req_charge_bytes i m in
  mmap_noreserve_backed_ok (in_arg i 3) m c = false
  \/ mmap_fixed_rw_budget_ok (in_arg i 3) m (in_arg i 0) (Z_to_bv 64 c) = false
  \/ mmap_fixed_rw_span_budget_ok (in_arg i 3) m (in_arg i 0) (Z_to_bv 64 c) = false.
Proof.
  intros i m Hno Hb c.
  assert (Hc : c = page_round_up_Z (bv_unsigned (in_arg i 1))).
  { subst c. unfold alloc_req_charge_bytes. cbv zeta. rewrite Hno. reflexivity. }
  rewrite Hc.
  unfold alloc_budget_refused_b in Hb. cbv zeta in Hb. rewrite Hno in Hb.
  cbn [Z.eqb Pos.eqb] in Hb.
  unfold mmap_budget_refused_b in Hb. cbv zeta in Hb.
  repeat match type of Hb with
         | context [if ?b then _ else _] => destruct b eqn:?; try discriminate Hb
         end;
    apply negb_true_iff in Hb;
    first [ left; exact Hb | right; left; exact Hb | right; right; exact Hb ].
Qed.

Lemma alloc_req_charge_mprotect : forall i m,
  bv_unsigned (in_sysno i) = 226%Z ->
  alloc_budget_refused_b i m = true ->
  mprotect_budget_ok m (in_arg i 0) (Z_to_bv 64 (alloc_req_charge_bytes i m)) = false.
Proof.
  intros i m Hno Hb.
  assert (Hc : alloc_req_charge_bytes i m = page_round_up_Z (bv_unsigned (in_arg i 1))).
  { unfold alloc_req_charge_bytes. cbv zeta. rewrite Hno. reflexivity. }
  rewrite Hc.
  unfold alloc_budget_refused_b in Hb. cbv zeta in Hb. rewrite Hno in Hb.
  cbn [Z.eqb Pos.eqb] in Hb.
  unfold mprotect_budget_refused_b in Hb. cbv zeta in Hb.
  repeat match type of Hb with
         | context [if ?b then _ else _] => destruct b eqn:?; try discriminate Hb
         end.
  apply negb_true_iff in Hb. exact Hb.
Qed.

(** [munmap] has no gate to tie a charge to: its mark never fires
    ([Mmap.munmap_budget_refused_b]), so no munmap request is
    budget-refused, whatever the state. *)
Lemma alloc_budget_refused_munmap : forall i m,
  bv_unsigned (in_sysno i) = 215%Z ->
  alloc_budget_refused_b i m = false.
Proof.
  intros i m Hno. unfold alloc_budget_refused_b. cbv zeta. rewrite Hno.
  reflexivity.
Qed.

Lemma lookup_injected_in : forall t n a,
  lookup_injected t n = Some a -> In a t /\ ia_no a = n.
Proof.
  induction t as [| x t IH]; intros n a H; [discriminate H |].
  cbn in H. destruct (Z.eqb (ia_no x) n) eqn:E.
  - injection H as <-. split; [left; reflexivity | apply Z.eqb_eq; exact E].
  - destruct (IH n a H) as [Hin Hno]. split; [right; exact Hin | exact Hno].
Qed.

(** Every [FamAlloc] arm is dispatched: by case analysis over the
    table, so an arm added to it under [FamAlloc] breaks this proof
    until [alloc_mark_sysnos] and the dispatcher carry its number. *)
Ltac in_alloc_mark_sysnos :=
  cbn [alloc_mark_sysnos In];
  first [ left; reflexivity
        | right; left; reflexivity
        | right; right; left; reflexivity
        | right; right; right; left; reflexivity
        | right; right; right; right; left; reflexivity ].

Lemma alloc_family_dispatched : forall no a,
  injected_arm no = Some a -> ia_family a = FamAlloc -> In no alloc_mark_sysnos.
Proof.
  intros no a H Hf.
  destruct (lookup_injected_in _ _ _ H) as [Hin <-].
  cbn [injected_table In] in Hin.
  repeat (destruct Hin as [<- | Hin];
          [cbn in Hf; first [discriminate Hf | in_alloc_mark_sysnos] |]).
  destruct Hin.
Qed.

(** ... every number ON the list is dispatched to its arm's mark — so a
    number added to [alloc_mark_sysnos] without a dispatcher arm goes red
    here rather than falling to the [false] default ... *)
Lemma alloc_mark_sysnos_dispatched : forall i m,
  let no := bv_unsigned (in_sysno i) in
  (no = 214%Z -> alloc_budget_refused_b i m = brk_budget_refused_b m (in_arg i 0))
  /\ (no = 215%Z ->
      alloc_budget_refused_b i m = munmap_budget_refused_b (in_arg i 0) (in_arg i 1) m)
  /\ (no = 216%Z ->
      alloc_budget_refused_b i m
      = mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m)
  /\ (no = 222%Z ->
      alloc_budget_refused_b i m
      = mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
          (in_arg i 4) (in_arg i 5) m)
  /\ (no = 226%Z ->
      alloc_budget_refused_b i m
      = mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) m).
Proof.
  intros i m no. unfold alloc_budget_refused_b. fold no.
  repeat split; intros E; rewrite E; reflexivity.
Qed.

(** ... and the dispatcher answers [false] exactly off the list, which
    ties [alloc_mark_sysnos] to the numbers it tests. *)
Lemma alloc_budget_refused_b_outside : forall i m,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  alloc_budget_refused_b i m = false.
Proof.
  intros i m Hout. unfold alloc_budget_refused_b. cbv zeta.
  destruct (Z.eqb (bv_unsigned (in_sysno i)) 214) eqn:E1;
    [apply Z.eqb_eq in E1; exfalso; apply Hout; rewrite E1; in_alloc_mark_sysnos |].
  destruct (Z.eqb (bv_unsigned (in_sysno i)) 215) eqn:E5;
    [apply Z.eqb_eq in E5; exfalso; apply Hout; rewrite E5; in_alloc_mark_sysnos |].
  destruct (Z.eqb (bv_unsigned (in_sysno i)) 216) eqn:E2;
    [apply Z.eqb_eq in E2; exfalso; apply Hout; rewrite E2; in_alloc_mark_sysnos |].
  destruct (Z.eqb (bv_unsigned (in_sysno i)) 222) eqn:E3;
    [apply Z.eqb_eq in E3; exfalso; apply Hout; rewrite E3; in_alloc_mark_sysnos |].
  destruct (Z.eqb (bv_unsigned (in_sysno i)) 226) eqn:E4;
    [apply Z.eqb_eq in E4; exfalso; apply Hout; rewrite E4; in_alloc_mark_sysnos |].
  reflexivity.
Qed.

(** The syscall [i] belongs to a family [cfg] reads as forced-only. *)
Definition injected_family_off (cfg : SpuriousCfg) (i : SyscallInput) : bool :=
  match injected_arm (bv_unsigned (in_sysno i)) with
  | Some a => negb (family_may_fail cfg (ia_family a))
  | None => false
  end.

(** The one decision a forced-only family adds to a syscall step: is
    this outcome a refusal the state did not force?  Three conjuncts —
    the family is off, the answer is a refusal, and the spec admits a
    non-refusal answer at the same input and model.  The third is what
    makes the filter exact; see this section's header. *)
Definition spurious_refusal_cfg (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) : Prop :=
  injected_family_off cfg i = true
  /\ refusal_b i m (eff_ret eff) = true
  /\ (exists eff' m' evs',
        syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false).

(** The question the KNOWN GAP is about, stated once: at [(i, m)], if
    the syscall's family is off in [cfg], then either a non-refusal
    outcome exists or every admissible outcome is a refusal.  Vacuous
    for a family that may fail and for a syscall that injects nothing;
    not decidable in general inside this tree for the rest — for [mmap]
    it is the placement question — which is why [sstep_cfg_progress]
    takes it as a premise rather than proving it. *)
Definition refusal_decided (cfg : SpuriousCfg) (i : SyscallInput) (m : Model) : Prop :=
  injected_family_off cfg i = true ->
  (exists eff' m' evs',
     syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false)
  \/ (forall eff' m' evs',
        syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true).

Lemma injected_family_off_may_fail : forall i,
  injected_family_off may_fail_cfg i = false.
Proof.
  intros i. unfold injected_family_off.
  destruct (injected_arm _) as [[no f es] |]; [destruct f |]; reflexivity.
Qed.

(** Under the may-fail reading nothing is spurious: that is what makes
    [may_fail_cfg] the reading every existing statement has. *)
Lemma spurious_refusal_may_fail : forall i m eff,
  ~ spurious_refusal_cfg may_fail_cfg i m eff.
Proof.
  intros i m eff (Hoff & _ & _).
  rewrite injected_family_off_may_fail in Hoff. discriminate Hoff.
Qed.

(** A non-refusal outcome is never spurious, whatever the configuration. *)
Lemma spurious_refusal_not_refusal : forall cfg i m eff,
  refusal_b i m (eff_ret eff) = false ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff Hnr (_ & Hr & _). congruence.
Qed.

(** ... and neither is any outcome of a family that may fail. *)
Lemma spurious_refusal_family_on : forall cfg i m eff,
  injected_family_off cfg i = false ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff Hon (Hoff & _ & _). congruence.
Qed.

(** Turning families off only makes more outcomes spurious. *)
Lemma spurious_refusal_mono : forall cfg1 cfg2 i m eff,
  cfg_le cfg1 cfg2 ->
  spurious_refusal_cfg cfg2 i m eff -> spurious_refusal_cfg cfg1 i m eff.
Proof.
  intros cfg1 cfg2 i m eff Hle (Hoff & Hr & Hex).
  split; [| split; [exact Hr | exact Hex]].
  unfold injected_family_off in *.
  destruct (injected_arm _) as [a |]; [| discriminate Hoff].
  destruct (family_may_fail cfg1 (ia_family a)) eqn:H1; [| reflexivity].
  rewrite (Hle _ H1) in Hoff. discriminate Hoff.
Qed.

Section StepCfg.
Variable segs : list Segment.

(** [sstep] under a configuration: every constructor is [sstep]'s, and
    the two that consume a syscall outcome additionally require the
    outcome not to be a spurious refusal.  The exit constructor needs no
    such premise — an exit is never a refusal — and neither does the
    fail-closed [Unmodeled] arm, which is not an outcome at all. *)
Inductive sstep_cfg (cfg : SpuriousCfg) : config -> list event -> step_to -> Prop :=
| sstep_cfg_instr : forall ms model ms' model',
    m_halted model = None ->
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineOk (ms', model') ->
    sstep_cfg cfg (mkCfg ms model) [] (SNext (mkCfg ms' model'))
| sstep_cfg_instr_fault : forall ms model,
    m_halted model = None ->
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineFault ->
    sstep_cfg cfg (mkCfg ms model) [] SError
| sstep_cfg_instr_unmodeled : forall ms model,
    m_halted model = None ->
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineUnmodeled ->
    sstep_cfg cfg (mkCfg ms model) [] SError
| sstep_cfg_syscall : forall ms model x8 eff model' model'' evs,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
    ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff ->
    m_halted model' = None ->
    materialize_model_accesses model' (syscall_effect_accesses eff)
      = Some model'' ->
    sstep_cfg cfg (mkCfg ms model) evs
          (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
| sstep_cfg_syscall_materialization_fault : forall ms model x8 eff model' evs,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
    ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff ->
    m_halted model' = None ->
    materialize_model_accesses model' (syscall_effect_accesses eff) = None ->
    sstep_cfg cfg (mkCfg ms model) [] SError
| sstep_cfg_exit : forall ms model x8 eff model' evs code,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
    m_halted model' = Some code ->
    m_killed model' = None ->
    sstep_cfg cfg (mkCfg ms model) (evs ++ [ExitEv code (m_fs model')])
          (SNext (mkCfg ms model'))
| sstep_cfg_killed : forall ms model x8 eff model' evs sig,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
    m_killed model' = Some sig ->
    sstep_cfg cfg (mkCfg ms model) (evs ++ [KillEv sig (m_fs model')])
          (SNext (mkCfg ms model'))
| sstep_cfg_syscall_unmodeled : forall ms model x8,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    syscall_spec (sys_input segs ms x8) model Unmodeled ->
    sstep_cfg cfg (mkCfg ms model) [] SError.

(** SUBSET: every filtered step is a step. *)
Lemma sstep_cfg_sub : forall cfg c evs r,
  sstep_cfg cfg c evs r -> sstep segs c evs r.
Proof.
  intros cfg c evs r H; destruct H;
    [ eapply sstep_instr | eapply sstep_instr_fault | eapply sstep_instr_unmodeled
    | eapply sstep_syscall | eapply sstep_syscall_materialization_fault
    | eapply sstep_exit | eapply sstep_killed | eapply sstep_syscall_unmodeled ];
    eauto.
Qed.

(** MEANING: at [may_fail_cfg] the two relations coincide. *)
Lemma sstep_cfg_may_fail : forall c evs r,
  sstep segs c evs r <-> sstep_cfg may_fail_cfg c evs r.
Proof.
  intros c evs r; split; intros H.
  - destruct H;
      [ eapply sstep_cfg_instr | eapply sstep_cfg_instr_fault
      | eapply sstep_cfg_instr_unmodeled
      | eapply sstep_cfg_syscall | eapply sstep_cfg_syscall_materialization_fault
      | eapply sstep_cfg_exit | eapply sstep_cfg_killed
      | eapply sstep_cfg_syscall_unmodeled ];
      eauto using spurious_refusal_may_fail.
  - exact (sstep_cfg_sub _ _ _ _ H).
Qed.

(** MONOTONE: a configuration that admits more families admits more
    steps. *)
Lemma sstep_cfg_mono : forall cfg1 cfg2 c evs r,
  cfg_le cfg1 cfg2 ->
  sstep_cfg cfg1 c evs r -> sstep_cfg cfg2 c evs r.
Proof.
  intros cfg1 cfg2 c evs r Hle H; destruct H;
    [ eapply sstep_cfg_instr | eapply sstep_cfg_instr_fault
    | eapply sstep_cfg_instr_unmodeled
    | eapply sstep_cfg_syscall | eapply sstep_cfg_syscall_materialization_fault
    | eapply sstep_cfg_exit | eapply sstep_cfg_killed
    | eapply sstep_cfg_syscall_unmodeled ];
    eauto using spurious_refusal_mono.
Qed.

(** PROGRESS, where the filter's question is answered: a configuration
    with a step has a filtered step.  The one case with content is a
    syscall outcome that the filter removes; then, by the third conjunct
    of [spurious_refusal_cfg], a non-refusal outcome exists at the same
    input and model, and that outcome — never spurious — is a step of
    one of the three syscall shapes.  Deciding WHICH case one is in is
    the premise; see [refusal_decided]. *)
Lemma sstep_cfg_progress : forall cfg ms model evs st,
  (forall x8, ms_svc_pending ms = Some x8 ->
              refusal_decided cfg (sys_input segs ms x8) model) ->
  sstep segs (mkCfg ms model) evs st ->
  exists evs' st', sstep_cfg cfg (mkCfg ms model) evs' st'.
Proof.
  intros cfg ms model evs st Hdec H.
  inversion H; subst.
  - eexists _, _. eapply sstep_cfg_instr; eassumption.
  - eexists _, _. eapply sstep_cfg_instr_fault; eassumption.
  - eexists _, _. eapply sstep_cfg_instr_unmodeled; eassumption.
  - (* a syscall outcome that materializes *)
    match goal with
    | [ Hsvc : ms_svc_pending ms = Some ?x8 |- _ ] =>
        destruct (injected_family_off cfg (sys_input segs ms x8)) eqn:Hoff;
        [ destruct (Hdec x8 Hsvc Hoff) as [(eff' & m' & evs' & Hspec' & Hnr) | Hall]
        | eexists _, _; eapply sstep_cfg_syscall; try eassumption;
          apply spurious_refusal_family_on; exact Hoff ]
    end.
    + (* a non-refusal outcome exists: it steps, whatever [eff] did *)
      pose proof (spurious_refusal_not_refusal cfg _ _ _ Hnr) as Hns.
      destruct (m_halted m') as [code |] eqn:Hh'.
      * destruct (m_killed m') as [sig |] eqn:Hk'.
        { eexists _, _. eapply sstep_cfg_killed; eassumption. }
        { eexists _, _. eapply sstep_cfg_exit; eassumption. }
      * destruct (materialize_model_accesses m' (syscall_effect_accesses eff'))
          as [m'' |] eqn:Hmat.
        { eexists _, _. eapply sstep_cfg_syscall; eassumption. }
        { eexists _, _. eapply sstep_cfg_syscall_materialization_fault; eassumption. }
    + (* every outcome is a refusal: none is spurious, so [eff] steps *)
      eexists _, _. eapply sstep_cfg_syscall; try eassumption.
      intros (_ & _ & (eff' & m' & evs' & Hspec' & Hnr)).
      rewrite (Hall _ _ _ Hspec') in Hnr. discriminate Hnr.
  - (* a syscall outcome whose materialization faults: the same split *)
    match goal with
    | [ Hsvc : ms_svc_pending ms = Some ?x8 |- _ ] =>
        destruct (injected_family_off cfg (sys_input segs ms x8)) eqn:Hoff;
        [ destruct (Hdec x8 Hsvc Hoff) as [(eff' & m' & evs' & Hspec' & Hnr) | Hall]
        | eexists _, _; eapply sstep_cfg_syscall_materialization_fault; try eassumption;
          apply spurious_refusal_family_on; exact Hoff ]
    end.
    + pose proof (spurious_refusal_not_refusal cfg _ _ _ Hnr) as Hns.
      destruct (m_halted m') as [code |] eqn:Hh'.
      * destruct (m_killed m') as [sig |] eqn:Hk'.
        { eexists _, _. eapply sstep_cfg_killed; eassumption. }
        { eexists _, _. eapply sstep_cfg_exit; eassumption. }
      * destruct (materialize_model_accesses m' (syscall_effect_accesses eff'))
          as [m'' |] eqn:Hmat.
        { eexists _, _. eapply sstep_cfg_syscall; eassumption. }
        { eexists _, _. eapply sstep_cfg_syscall_materialization_fault; eassumption. }
    + eexists _, _. eapply sstep_cfg_syscall_materialization_fault; try eassumption.
      intros (_ & _ & (eff' & m' & evs' & Hspec' & Hnr)).
      rewrite (Hall _ _ _ Hspec') in Hnr. discriminate Hnr.
  - eexists _, _. eapply sstep_cfg_exit; eassumption.
  - eexists _, _. eapply sstep_cfg_killed; eassumption.
  - eexists _, _. eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

Inductive star_cfg (cfg : SpuriousCfg) : config -> list event -> config -> Prop :=
| star_cfg_refl : forall c, star_cfg cfg c [] c
| star_cfg_step : forall c1 evs c2 tr c3,
    sstep_cfg cfg c1 evs (SNext c2) ->
    star_cfg cfg c2 tr c3 ->
    star_cfg cfg c1 (evs ++ tr) c3.

Lemma star_cfg_sub : forall cfg c tr c',
  star_cfg cfg c tr c' -> star segs c tr c'.
Proof.
  intros cfg c tr c' H; induction H;
    [apply star_refl | eapply star_step; eauto using sstep_cfg_sub].
Qed.

Lemma star_cfg_may_fail : forall c tr c',
  star segs c tr c' <-> star_cfg may_fail_cfg c tr c'.
Proof.
  intros c tr c'; split; intros H.
  - induction H; [apply star_cfg_refl |].
    eapply star_cfg_step; [apply sstep_cfg_may_fail; eassumption | assumption].
  - exact (star_cfg_sub _ _ _ _ H).
Qed.

Definition obs_trace_cfg (cfg : SpuriousCfg) (c0 : config) (tr : list event) : Prop :=
  exists tr' c, star_cfg cfg c0 tr' c /\ is_prefix tr tr'.

Definition reaches_error_cfg (cfg : SpuriousCfg) (c0 : config) : Prop :=
  exists tr c evs, star_cfg cfg c0 tr c /\ sstep_cfg cfg c evs SError.

Inductive all_traces_error_cfg (cfg : SpuriousCfg) : config -> Prop :=
| all_traces_error_cfg_intro : forall c,
    (exists evs to, sstep_cfg cfg c evs to) ->
    (forall evs c', sstep_cfg cfg c evs (SNext c') -> all_traces_error_cfg cfg c') ->
    all_traces_error_cfg cfg c.

Definition reaches_unmodeled_cfg (cfg : SpuriousCfg) (c0 : config) : Prop :=
  exists tr c, star_cfg cfg c0 tr c /\ unmodeled_at segs c.

(** The filtered run removes executions and adds none: every trace,
    error and uncovered point of the filtered run is one of the run's.
    [all_traces_error_cfg] is deliberately absent from this list — it is
    a universal over successors, so fewer steps do not give it in either
    direction — and [Equivalence.equiv]'s escape is stated on it, which
    is one more reason a proof at one configuration says nothing at
    another. *)
Lemma obs_trace_cfg_sub : forall cfg c0 tr,
  obs_trace_cfg cfg c0 tr -> obs_trace segs c0 tr.
Proof.
  intros cfg c0 tr (tr' & c & Hs & Hp); exists tr', c; eauto using star_cfg_sub.
Qed.

Lemma reaches_error_cfg_sub : forall cfg c0,
  reaches_error_cfg cfg c0 -> reaches_error segs c0.
Proof.
  intros cfg c0 (tr & c & evs & Hs & He); exists tr, c, evs;
    eauto using star_cfg_sub, sstep_cfg_sub.
Qed.

Lemma reaches_unmodeled_cfg_sub : forall cfg c0,
  reaches_unmodeled_cfg cfg c0 -> reaches_unmodeled segs c0.
Proof.
  intros cfg c0 (tr & c & Hs & Hu); exists tr, c; eauto using star_cfg_sub.
Qed.

(** ... and at [may_fail_cfg] each of the four is the unfiltered one. *)
Lemma obs_trace_cfg_may_fail : forall c0 tr,
  obs_trace segs c0 tr <-> obs_trace_cfg may_fail_cfg c0 tr.
Proof.
  intros c0 tr; split; intros (tr' & c & Hs & Hp); exists tr', c;
    (split; [apply star_cfg_may_fail; exact Hs | exact Hp]).
Qed.

Lemma reaches_error_cfg_may_fail : forall c0,
  reaches_error segs c0 <-> reaches_error_cfg may_fail_cfg c0.
Proof.
  intros c0; split; intros (tr & c & evs & Hs & He); exists tr, c, evs;
    (split; [apply star_cfg_may_fail; exact Hs | apply sstep_cfg_may_fail; exact He]).
Qed.

Lemma all_traces_error_cfg_may_fail : forall c,
  all_traces_error segs c <-> all_traces_error_cfg may_fail_cfg c.
Proof.
  intros c; split; intros H.
  - induction H as [c (evs & to & Hstep) _ IH].
    constructor.
    + exists evs, to. apply sstep_cfg_may_fail; exact Hstep.
    + intros evs' c' Hss. apply (IH evs' c'). apply sstep_cfg_may_fail; exact Hss.
  - induction H as [c (evs & to & Hstep) _ IH].
    constructor.
    + exists evs, to. apply sstep_cfg_may_fail; exact Hstep.
    + intros evs' c' Hss. apply (IH evs' c'). apply sstep_cfg_may_fail; exact Hss.
Qed.

Lemma reaches_unmodeled_cfg_may_fail : forall c0,
  reaches_unmodeled segs c0 <-> reaches_unmodeled_cfg may_fail_cfg c0.
Proof.
  intros c0; split; intros (tr & c & Hs & Hu); exists tr, c;
    (split; [apply star_cfg_may_fail; exact Hs | exact Hu]).
Qed.

(** Being uncovered is a special case of erroring under every
    configuration, as it is under none: both uncovered shapes are
    premises of an [SError] transition that no filter touches. *)
Lemma reaches_unmodeled_cfg_reaches_error_cfg : forall cfg c0,
  reaches_unmodeled_cfg cfg c0 -> reaches_error_cfg cfg c0.
Proof.
  intros cfg c0 (tr & [ms model] & Hstar & Hh & [(Hsvc & Hacc) | (x8 & Hsvc & Hspec)]);
    cbn [cfg_ms cfg_model] in *.
  - exists tr, (mkCfg ms model), []. split; [exact Hstar |].
    apply sstep_cfg_instr_unmodeled; assumption.
  - exists tr, (mkCfg ms model), []. split; [exact Hstar |].
    apply (sstep_cfg_syscall_unmodeled cfg ms model x8); assumption.
Qed.

Lemma all_traces_error_cfg_reaches_error_cfg : forall cfg c,
  all_traces_error_cfg cfg c -> reaches_error_cfg cfg c.
Proof.
  intros cfg c Hall. induction Hall as [c Hprogress Hnext IH].
  destruct Hprogress as (evs & to & Hstep). destruct to as [c' |].
  - destruct (IH evs c' Hstep) as (tr & c2 & err_evs & Hstar & Herr).
    exists (evs ++ tr), c2, err_evs. split; [| exact Herr].
    econstructor; eauto.
  - exists [], c, evs. split; [apply star_cfg_refl | exact Hstep].
Qed.

End StepCfg.

(** [run] under a spurious-failure configuration: the same initial
    configuration, the same four observations, over the filtered step
    relation.  Written as the same [match] as [run] and for the same
    reason. *)
Definition run_scfg (cfg : SpuriousCfg) (img : Image) (lim : Z) (en : ExecEntry)
    (inp : ProcInput) : behavior :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    let c0 := init_config segs pc ph sp brk0 mbase rnd lim inp in
    {| bh_traces := obs_trace_cfg segs cfg c0;
       bh_errors := reaches_error_cfg segs cfg c0;
       bh_all_errors := all_traces_error_cfg segs cfg c0;
       bh_unmodeled := reaches_unmodeled_cfg segs cfg c0 |}
  end.

(** Two behaviors that agree observation by observation.  [behavior]
    is a record of bare [Prop]s, so this is the relation under which
    [run] and [run_scfg may_fail_cfg] are the same thing — propositional
    equality of the records would need extensionality this tree does
    not assume. *)
Definition behavior_equiv (b1 b2 : behavior) : Prop :=
  (forall tr, bh_traces b1 tr <-> bh_traces b2 tr)
  /\ (bh_errors b1 <-> bh_errors b2)
  /\ (bh_all_errors b1 <-> bh_all_errors b2)
  /\ (bh_unmodeled b1 <-> bh_unmodeled b2).

Lemma behavior_equiv_refl : forall b, behavior_equiv b b.
Proof. intros b. repeat split; auto. Qed.

Lemma behavior_equiv_sym : forall b1 b2, behavior_equiv b1 b2 -> behavior_equiv b2 b1.
Proof.
  intros b1 b2 (Ht & He & Ha & Hu).
  split; [intros tr; symmetry; apply Ht |].
  split; [symmetry; exact He |]. split; symmetry; assumption.
Qed.

(** MEANING PRESERVED: [run_scfg may_fail_cfg] is [run], observation by
    observation.  This is what lets every statement above this section
    keep its text: it is the [may_fail_cfg] instance of its [_scfg]
    form ([Equivalence.strong_universal_T_scfg_may_fail] and its
    siblings). *)
Lemma run_scfg_may_fail : forall img lim en inp,
  behavior_equiv (run_scfg may_fail_cfg img lim en inp) (run img lim en inp).
Proof.
  intros [segs pc ph] lim [sp brk0 mbase] inp.
  cbn [run_scfg run bh_traces bh_errors bh_all_errors bh_unmodeled].
  split; [intros tr; symmetry; apply obs_trace_cfg_may_fail |].
  split; [symmetry; apply reaches_error_cfg_may_fail |].
  split; [symmetry; apply all_traces_error_cfg_may_fail |].
  symmetry; apply reaches_unmodeled_cfg_may_fail.
Qed.

(** The run with every avoidable allocation refusal removed and every
    other family left at may-fail: [alloc_may_fail = false]. *)
Definition run_nospurious (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput)
    : behavior :=
  run_scfg (alloc_only_cfg false) img lim en inp.

(** The one-switch form.  Written as an [if] on the literal so
    that [run_cfg true] is [run] BY CONVERSION — every statement and
    library lemma about [run] applies to the [true] instance with no
    bridge — and [run_cfg false] is [run_nospurious].  A proof stated
    over [run_cfg b] for a variable [b] reaches the record form through
    [run_cfg_scfg]. *)
Definition run_cfg (alloc_may_fail : bool) (img : Image) (lim : Z)
    (en : ExecEntry) (inp : ProcInput) : behavior :=
  if alloc_may_fail then run img lim en inp else run_nospurious img lim en inp.

Lemma run_cfg_true : forall img lim en inp,
  run_cfg true img lim en inp = run img lim en inp.
Proof. reflexivity. Qed.

Lemma run_cfg_false : forall img lim en inp,
  run_cfg false img lim en inp = run_nospurious img lim en inp.
Proof. reflexivity. Qed.

Lemma run_cfg_scfg : forall b img lim en inp,
  behavior_equiv (run_cfg b img lim en inp) (run_scfg (alloc_only_cfg b) img lim en inp).
Proof.
  intros [|] img lim en inp; cbn [run_cfg].
  - apply behavior_equiv_sym, run_scfg_may_fail.
  - apply behavior_equiv_refl.
Qed.

(** SUBSET, at the level of behaviors: whatever the configuration, the
    filtered run's traces, errors and uncovered points are the run's. *)
Lemma run_scfg_sub_traces : forall cfg img lim en inp tr,
  bh_traces (run_scfg cfg img lim en inp) tr -> bh_traces (run img lim en inp) tr.
Proof.
  intros cfg [segs pc ph] lim [sp brk0 mbase] inp tr H.
  cbn [run_scfg run bh_traces] in *. eapply obs_trace_cfg_sub; exact H.
Qed.

Lemma run_scfg_sub_errors : forall cfg img lim en inp,
  bh_errors (run_scfg cfg img lim en inp) -> bh_errors (run img lim en inp).
Proof.
  intros cfg [segs pc ph] lim [sp brk0 mbase] inp H.
  cbn [run_scfg run bh_errors] in *. eapply reaches_error_cfg_sub; exact H.
Qed.

Lemma run_scfg_sub_unmodeled : forall cfg img lim en inp,
  bh_unmodeled (run_scfg cfg img lim en inp) -> bh_unmodeled (run img lim en inp).
Proof.
  intros cfg [segs pc ph] lim [sp brk0 mbase] inp H.
  cbn [run_scfg run bh_unmodeled] in *. eapply reaches_unmodeled_cfg_sub; exact H.
Qed.

(** The behavior-level images of the two containments [Run.run]
    realises, restated for the filtered run so that
    [Equivalence.error_free] keeps subsuming [Equivalence.modeled] under
    every configuration. *)
Lemma run_scfg_unmodeled_errors : forall cfg img lim en inp,
  bh_unmodeled (run_scfg cfg img lim en inp) -> bh_errors (run_scfg cfg img lim en inp).
Proof.
  intros cfg [segs pc ph] lim [sp brk0 mbase] inp H.
  cbn [run_scfg bh_unmodeled bh_errors] in *.
  eapply reaches_unmodeled_cfg_reaches_error_cfg; exact H.
Qed.

Lemma run_scfg_all_errors_errors : forall cfg img lim en inp,
  bh_all_errors (run_scfg cfg img lim en inp) -> bh_errors (run_scfg cfg img lim en inp).
Proof.
  intros cfg [segs pc ph] lim [sp brk0 mbase] inp H.
  cbn [run_scfg bh_all_errors bh_errors] in *.
  eapply all_traces_error_cfg_reaches_error_cfg; exact H.
Qed.

(* =========================================================================
   The budget mark: where a run is refused for exceeding its budget
   =========================================================================

   [Equivalence.strong_universal_T_budgets] and its siblings state the
   flavour-pair obligation (the same program built plain and with a
   sanitizer) for the inputs on which the SOURCE run, under the source
   budget, never takes a budget-refused allocation.  This section
   defines that observable.  It is a PREDICATE over the configurations
   a run reaches — not a trace event, which would enter trace equality
   and change what every statement above means, and not a state flag,
   which nothing could set on the first-touch path below, where the
   refusal IS the error transition and there is no successor state.
   Nothing above this section changes.

   A configuration is budget-refused when the run is about to be
   declined for exceeding [State.vm_limit], in one of three ways:

   - the pending INSTRUCTION touches a lazy page the budget cannot back:
     the interpreter answers [MachineOk] (the access itself is fine) and
     [State.materialize_model_accesses] answers [None], which
     [State.materialize_accesses] does in exactly one case — a newly
     touched page would push the charge above the limit.  A
     [MachineFault] from the interpreter (a bad address, [ebreak]) is
     therefore NOT budget-refused, although both go to [SError] through
     [sstep_instr_fault];
   - the pending SYSCALL is a grant the budget refuses:
     [alloc_budget_refused_b] on the request and the pre-state, a
     boolean each arm defines beside its spec as the negation of its
     own budget gate ([munmap], which has no gate, defines the constant
     [false]).  It reads the request and the state, never the answer:
     the arms that consult a budget keep an [alt] onto their errno list,
     so a refusal is always ADMISSIBLE, and what the mark says is that at
     this configuration nothing else is;
   - some admissible outcome of the pending syscall has an effect
     whose copy-in or copy-out touches a lazy page the budget cannot
     back — the [sstep_syscall_materialization_fault] premises.

   The first and third are premises of an [SError] transition
   ([budget_fault_instr_sstep_error], [budget_fault_syscall_sstep_error]);
   the second is not an error at all — the program is answered -ENOMEM
   or the old break and goes on — which is why the premise is a
   separate observable rather than a reading of [bh_errors].

   On a run with no MAP_NORESERVE mapping — every plain musl build —
   [State.m_vm_lazy] is empty at every reachable state and the two
   first-touch clauses are false ([materialize_model_accesses_no_lazy]),
   so discharging the premise is the grant clause at each ecall
   ([budget_refused_at_no_lazy_instr], [budget_refused_at_no_lazy_syscall]).
   ========================================================================= *)

Section Budget.
Variable segs : list Segment.

Definition budget_refused_at (c : config) : Prop :=
  m_halted (cfg_model c) = None /\
  ( (ms_svc_pending (cfg_ms c) = None /\
     exists report,
       RiscvSemantics.step_accesses segs (cfg_ms c) = MachineOk report /\
       materialize_model_accesses (cfg_model c) (@accessed_ranges _ report) = None)
  \/ (exists x8, ms_svc_pending (cfg_ms c) = Some x8 /\
       ( alloc_budget_refused_b (sys_input segs (cfg_ms c) x8) (cfg_model c) = true
       \/ exists eff model' evs,
            syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) (Ok eff model' evs)
            /\ m_halted model' = None
            /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None)) ).

(** The run can reach a budget-refused configuration. *)
Definition reaches_budget_refused (c0 : config) : Prop :=
  exists tr c, star segs c0 tr c /\ budget_refused_at c.

Lemma reaches_budget_refused_intro : forall c,
  budget_refused_at c -> reaches_budget_refused c.
Proof. intros c H. exists [], c. split; [apply star_refl | exact H]. Qed.

Lemma reaches_budget_refused_star : forall c0 tr c,
  star segs c0 tr c -> reaches_budget_refused c -> reaches_budget_refused c0.
Proof.
  intros c0 tr c Hstar (tr' & c' & Hstar' & Hb).
  exists (tr ++ tr'), c'. split; [exact (star_trans _ _ _ _ _ _ Hstar Hstar') | exact Hb].
Qed.

(** The two first-touch clauses are premises of an error transition. *)
Lemma budget_fault_instr_sstep_error : forall ms model report,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk report ->
  materialize_model_accesses model (@accessed_ranges _ report) = None ->
  sstep segs (mkCfg ms model) [] SError.
Proof.
  intros ms model report Hh Hsvc Hstep Hmat.
  apply sstep_instr_fault; [exact Hh | exact Hsvc |].
  unfold mi_account_step. rewrite Hstep, Hmat. reflexivity.
Qed.

Lemma budget_fault_syscall_sstep_error : forall ms model x8 eff model' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  m_halted model' = None ->
  materialize_model_accesses model' (syscall_effect_accesses eff) = None ->
  sstep segs (mkCfg ms model) [] SError.
Proof.
  intros. eapply sstep_syscall_materialization_fault; eassumption.
Qed.

(** Discharging the premise: an invariant of the reachable
    configurations that excludes the mark. *)
Lemma star_invariant : forall (I : config -> Prop),
  (forall c evs c', I c -> sstep segs c evs (SNext c') -> I c') ->
  forall c0 tr c, star segs c0 tr c -> I c0 -> I c.
Proof.
  intros I Hstep c0 tr c Hstar. induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH].
  - exact (fun H => H).
  - intros H1. exact (IH (Hstep _ _ _ H1 Hss)).
Qed.

Lemma never_budget_refused_ind : forall (I : config -> Prop) c0,
  I c0 ->
  (forall c evs c', I c -> sstep segs c evs (SNext c') -> I c') ->
  (forall c, I c -> ~ budget_refused_at c) ->
  ~ reaches_budget_refused c0.
Proof.
  intros I c0 H0 Hstep Hno (tr & c & Hstar & Hb).
  exact (Hno c (star_invariant I Hstep c0 tr c Hstar H0) Hb).
Qed.

(** With no lazy mapping, an instruction configuration is never
    budget-refused: the first-touch clause needs [None] where
    [materialize_model_accesses_no_lazy] answers [Some], and the other
    two need a pending syscall. *)
Lemma budget_refused_at_no_lazy_instr : forall ms model,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  ~ budget_refused_at (mkCfg ms model).
Proof.
  intros ms model Hlazy Hsvc (_ & [(_ & report & _ & Hmat) | (x8 & Hx8 & _)]);
    cbn [cfg_ms cfg_model] in *.
  - rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat. discriminate Hmat.
  - congruence.
Qed.

(** ... and a syscall configuration whose every outcome leaves no lazy
    mapping either is budget-refused exactly by the grant clause. *)
Lemma budget_refused_at_no_lazy_syscall : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff model' evs,
     syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
     m_vm_lazy model' = []) ->
  (budget_refused_at (mkCfg ms model)
   <-> alloc_budget_refused_b (sys_input segs ms x8) model = true).
Proof.
  intros ms model x8 Hh Hsvc Hlazy. split.
  - intros (_ & [(Hnone & _) | (y8 & Hy8 & [Hb | (eff & model' & evs & Hspec & _ & Hmat)])]);
      cbn [cfg_ms cfg_model] in *.
    + congruence.
    + rewrite Hsvc in Hy8. injection Hy8 as <-. exact Hb.
    + rewrite Hsvc in Hy8. injection Hy8 as <-.
      rewrite (materialize_model_accesses_no_lazy model' _ (Hlazy _ _ _ Hspec)) in Hmat.
      discriminate Hmat.
  - intros Hb. split; [exact Hh |]. right. exists x8. split; [exact Hsvc |]. left. exact Hb.
Qed.


(** The same reachability under a configuration: [star_cfg] in place
    of [star], the mark unchanged.  The mark's instruction and grant
    clauses read the state and the request and see no configuration;
    its effect clause ranges over ALL the arm's admitted outcomes,
    including ones the configuration filters out, so under a
    configuration that clause can fire on the materialization fault of
    an outcome the configured run never takes — an over-approximation
    of "the configured run is about to be refused", in the safe
    direction (the premise is false more often, never true wrongly).
    What the configuration changes otherwise is WHICH configurations
    the run reaches: fewer, never more ([reaches_budget_refused_cfg_sub]),
    so the unfiltered premise discharges the configured one, and at
    [may_fail_cfg] the configured reachability is the unfiltered one
    ([reaches_budget_refused_cfg_may_fail]).  Where the GRANT clause
    fires on a brk, mmap or mprotect request, the filter removes nothing
    at all — every admitted outcome is a refusal, so none is spurious —
    which [Checks.BudgetPremise.marked_step_is_configured] states for
    exactly those arms.  Not for mremap: where its mark fires, the
    in-place resolution is never admitted, but the moved one is shown
    refused only at destinations that carry no backing metadata
    ([Checks.BudgetPremise.mremap_budget_refused_refuses_move]).  Its fit
    hypothesis and the protected ledger it reads are proved invariants
    ([Checks.MapsFit], [Checks.NoaccessOwned]); the lazy-ledger half is
    not yet proved preserved.  On a state with empty lazy ledgers every
    admitted outcome is a refusal
    ([Checks.BudgetPremiseMremap.mremap_budget_refused_is_refusal_sys_inv]).
    On a state that broke the lazy-ledger half, the mark could fire
    where a move is still admitted, and under a forced-only configuration
    the filter could drop the marked refusal as spurious; the marked
    configuration is still reached, so the premise is unaffected. *)
Definition reaches_budget_refused_cfg (cfg : SpuriousCfg) (c0 : config) : Prop :=
  exists tr c, star_cfg segs cfg c0 tr c /\ budget_refused_at c.

Lemma reaches_budget_refused_cfg_sub : forall cfg c0,
  reaches_budget_refused_cfg cfg c0 -> reaches_budget_refused c0.
Proof.
  intros cfg c0 (tr & c & Hstar & Hb).
  exists tr, c. split; [exact (star_cfg_sub segs cfg _ _ _ Hstar) | exact Hb].
Qed.

Lemma reaches_budget_refused_cfg_may_fail : forall c0,
  reaches_budget_refused c0 <-> reaches_budget_refused_cfg may_fail_cfg c0.
Proof.
  intros c0. split; intros (tr & c & Hstar & Hb); exists tr, c; split; try exact Hb.
  - apply star_cfg_may_fail; exact Hstar.
  - apply star_cfg_may_fail; exact Hstar.
Qed.

End Budget.

(** The run-level form: the [match] of [run], on the same initial
    configuration.  [Equivalence.source_within_budget] negates it. *)
Definition run_budget_refused (img : Image) (lim : Z) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    reaches_budget_refused segs (init_config segs pc ph sp brk0 mbase rnd lim inp)
  end.

(** The configured run's form, the [match] of [run_scfg]. *)
Definition run_scfg_budget_refused (cfg : SpuriousCfg) (img : Image) (lim : Z)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    reaches_budget_refused_cfg segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp)
  end.

Lemma run_scfg_budget_refused_sub : forall cfg img lim en inp,
  run_scfg_budget_refused cfg img lim en inp -> run_budget_refused img lim en inp.
Proof.
  intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp H.
  exact (reaches_budget_refused_cfg_sub segs cfg _ H).
Qed.

Lemma run_scfg_budget_refused_may_fail : forall img lim en inp,
  run_budget_refused img lim en inp <-> run_scfg_budget_refused may_fail_cfg img lim en inp.
Proof.
  intros [segs pc ph] lim [sp brk0 mbase rnd] inp.
  exact (reaches_budget_refused_cfg_may_fail segs _).
Qed.

(* =========================================================================
   Valid process inputs: argv and envp
   =========================================================================

   What [execve] hands a process — part of the Linux process model, not
   of any particular equivalence task.  The bounds keep the initial
   stack image comfortably inside the 8 MiB stack.  No
   byte-range clause ([b < 256]) is needed: the [byte] type enforces it.

   The other two [run] inputs: the initial file-system image is
   validated by [Fs.valid_fs]; the standard input stream
   ([State.InputStream]) needs no validity predicate at all — its
   elements are [byte], and any colist of bytes, finite or infinite, is
   an input a process could really be handed. *)

(** Validity predicate for the initial stack pointer: any 16-byte-aligned
    (riscv64 psABI entry guarantee) address in the window
    [[sp_window_lo, sp_window_hi]] (State.v).  Quantified independently
    per binary in [Equivalence.strong_universal_T] — the model's ASLR. *)
Definition valid_sp (sp : word) : Prop :=
  (sp_window_lo <= bv_unsigned sp)%Z /\ (bv_unsigned sp <= sp_window_hi)%Z /\
  (bv_unsigned sp mod 16 = 0)%Z.

(** Validity predicate for the initial program break ([mi_init_brk]).
    Its ASLR window is IMAGE-RELATIVE (unlike the SP's absolute window):
    any page-aligned address from the page-rounded image top
    ([State.reserved_top] of the LOAD reservations) up to [brk_aslr_max]
    above (covering the kernel's
    one-page gap plus up-to-1-GiB randomization,
    [arch_randomize_brk]/[randomize_page(_, SZ_1G)]).  Quantified
    independently per binary in [Equivalence.strong_universal_T] — the
    model's brk ASLR, mirroring [valid_sp]. *)
Definition valid_brk (segs : list Segment) (brk : word) : Prop :=
  (reserved_top (segments_reserved segs) <= bv_unsigned brk)%Z
  /\ (bv_unsigned brk <= reserved_top (segments_reserved segs) + brk_aslr_max)%Z
  /\ (bv_unsigned brk mod page_size = 0)%Z.

(** Validity predicate for the run's [mm->mmap_base] ([mi_mmap_base]):
    any page-aligned address in [[State.mmap_base_min,
    State.mmap_base_max]].  The floor is the smallest base a covered
    kernel's top-down layout computes and the cap the largest, both
    derived from mm/util.c's [mmap_base] on their own definitions, under
    two assumptions SCOPE.md names: the top-down layout, and
    [vm.mmap_rnd_bits] at most 24 or [stack_guard_gap] at most
    0x4aba6a2ab000 bytes (about 74.7 TiB).
    Under them the band is EXACTLY the set of bases Linux gives:
    [Checks.Cases.MmapBase.sv48_band_is_linux_set] proves both
    inclusions against a Rocq statement of that computation, so an error
    in either constant fails the build.  Outside them Linux can give a
    base under the floor, and the model has no entry for that launch.
    Quantified independently per binary in
    [Equivalence.strong_universal_T], like [valid_sp] and [valid_brk].

    The spec reads [vm_mmap_base]: it is the top-down bound of
    [Mmap.linux_place], through [State.mmap_top].  So the band is the
    set of placements the model admits, base by base.  Also,
    [valid_mmap_base] is the third conjunct of [valid_entry], which
    [Equivalence.strong_universal_T] quantifies its entries under, and
    discharging it is a required step of the tree's anti-vacuity lemma
    [Equivalence.image_brk_satisfiable_entry]: that lemma exhibits an
    entry and must show its base admissible.  Outside the spec, the ASan
    plan checker ([Common.AsanInit]) takes this predicate as a
    hypothesis and needs its floor; that is why the floor is not lowered
    to drop the assumptions (see [State.mmap_base_min]). *)
Definition valid_mmap_base (mbase : word) : Prop :=
  (mmap_base_min <= bv_unsigned mbase)%Z
  /\ (bv_unsigned mbase <= mmap_base_max)%Z
  /\ (bv_unsigned mbase mod page_size = 0)%Z.

(** * The same three predicates for a DECLARED address-space size

    [valid_sp] and [valid_mmap_base] above are the Sv48 instances, in
    the literal numbers the rest of the tree was written against.  The
    two below take the size the task declares ([State.VaSize]) and read
    the window and the band off it, by the derivations [State.va_stack_top]
    cites; [Checks.Cases.VaSize] pins that the [Sv48] instance is the
    literal one.  [valid_brk] has no such twin: the break's window is
    image-relative and the kernel's [arch_randomize_brk] does not read the
    depth. *)
Definition valid_sp_va (v : VaSize) (sp : word) : Prop :=
  (va_sp_window_lo v <= bv_unsigned sp)%Z
  /\ (bv_unsigned sp <= va_sp_window_hi v)%Z
  /\ (bv_unsigned sp mod 16 = 0)%Z.

Definition valid_mmap_base_va (v : VaSize) (mbase : word) : Prop :=
  (va_mmap_base_min v <= bv_unsigned mbase)%Z
  /\ (bv_unsigned mbase <= va_mmap_base_max v)%Z
  /\ (bv_unsigned mbase mod page_size = 0)%Z.

Lemma valid_sp_va_sv48 : forall sp, valid_sp_va Sv48 sp <-> valid_sp sp.
Proof.
  intros sp.
  unfold valid_sp_va, valid_sp, va_sp_window_lo, va_sp_window_hi, va_stack_top,
    sp_window_lo, sp_window_hi.
  lia.
Qed.

Lemma valid_mmap_base_va_sv48 : forall mb,
  valid_mmap_base_va Sv48 mb <-> valid_mmap_base mb.
Proof.
  intros mb.
  unfold valid_mmap_base_va, valid_mmap_base, va_mmap_base_min, va_mmap_base_max,
    va_stack_top, mmap_base_max, mmap_base_min, sp_window_hi.
  lia.
Qed.


(** Total bytes consumed by a list of argument strings
    (each string length + 1 for the null terminator), in [Z] like the
    rest of the range arithmetic. *)
Definition total_arg_bytes (args : list (list byte)) : Z :=
  fold_right (fun a acc => Z.of_nat (length a) + 1 + acc)%Z 0%Z args.

(** Validity predicate for argv lists.
    At least one argument is required: modern Linux never delivers
    argc = 0 (kernel commit dcd46d897adb rewrites an empty [execve]
    argv to a single empty string), so a process may rely on argv[0]
    existing — though not on it being nonempty.

    THE FIFTH CLAUSE IS NOT A FACT ABOUT LINUX, and it is the only one
    here that is not.  The first four say what a kernel can deliver:
    Linux itself bounds argc, the total byte count and each string, and
    NUL is what terminates a string so no argument can contain one.  A
    real [execve] delivers "/etc/passwd" and ".." without complaint, and
    this clause excludes both.  It is a NARROWING OF THE THEOREM'S
    DOMAIN, written where the domain is stated, and it is here because
    of what it buys:

    [Sys.Fs.Open.openat_resolved_spec] declines a pathname with a
    separator in it, because answering it at all would mean answering it
    WRONGLY — the create shapes would mint a flat key where Linux returns
    -ENOENT.  The whole-program examples in [Examples.cp_ns] and
    [Examples.headcp_ns] pass argv entries straight to [openat], so
    without this clause that declined arm is reachable under
    [valid_input], and since [Equivalence.modeled] is a conjunct of
    [strong_equiv]'s CONCLUSION rather than a hypothesis,
    [Equivalence.strong_universal_T] would be FALSE for both of them
    rather than merely narrower.

    THE ".." HALF IS NOT ABOUT SOUNDNESS.  [openat] ANSWERS ".." — it is
    a directory reference and takes the same arm "." does
    ([Open.path_is_dirref]), which is correct for every program and
    creates no [unmodeled] arm at all.  What the examples cannot absorb
    is the SHAPE of that answer: their case split is empty / "." /
    regular, so a ".." argument would take the dot arm while the regular
    branch's proof assumes the other one.  Widening the split costs
    about thirty concrete-path proof sites across four files, where the
    dot-family lemmas substitute the path with [dot_path] and compute on
    it.  So this half narrows the two THEOREMS without narrowing the
    model, and it would be deleted by proof work alone.

    IT IS ON THE TAIL, NOT THE WHOLE LIST, and that is load-bearing
    rather than tidy.  argv[0] conventionally holds a path — every shell
    launch puts one there — so a whole-list clause would restrict
    [strong_universal_T] to launches no shell performs, which is a far
    worse trade than the one being made.  Both examples read [nth 1] and
    [nth 2], so the tail is enough.  On a one-element argv the clause is
    vacuous ([tl] of a singleton is []), which is the right reading: a
    process launched with argv[0] alone opens nothing out of it.

    WHAT IT COSTS.  Every claim [strong_universal_T] makes is silent
    about a launch where any argument AFTER argv[0] contains a
    separator, or is exactly "..".  For a program that takes paths that
    is most real invocations: [cp src dst] is covered, [cp /tmp/src dst]
    is not.  That is priority 3 paid for priority 1.  The
    clause is stated over every tail entry rather than the two an
    example opens, because [valid_argv] does not know which entries a
    program will treat as a path — so it also excludes launches whose
    slash-bearing argument is never opened at all, which costs coverage
    for no soundness reason.

    It is deliberately NOT written in terms of [openat]: a validity
    predicate that named one syscall's policy would go stale the moment
    the policy moved.  What it says is a property of the strings. *)
Definition valid_argv (argv : list (list byte)) : Prop :=
  (1 <= Z.of_nat (length argv) <= 1024)%Z /\
  (total_arg_bytes argv <= 2097152)%Z /\
  Forall (fun a => (Z.of_nat (length a) <= 131071)%Z) argv /\
  Forall (fun a => ~ In (Z_to_bv 8 0) a) argv /\
  Forall (fun a => path_has_slash a = false
                   /\ path_eqb a dotdot_path = false) (tl argv).

(** Validity predicate for envp lists.
    Same structural constraints as argv but with larger bounds:
    up to 256 variables, 131072 bytes total. *)
Definition valid_envp (envp : list (list byte)) : Prop :=
  (Z.of_nat (length envp) <= 256)%Z /\
  (total_arg_bytes envp <= 131072)%Z /\
  Forall (fun e => (Z.of_nat (length e) <= 131071)%Z) envp /\
  Forall (fun e => ~ In (Z_to_bv 8 0) e) envp.

(** * The exec file name, and the launches Linux refuses with E2BIG

    ** Which names [execve] can present

    [bprm->filename] is either the caller's own path or a name
    [alloc_bprm] (fs/exec.c, Linux v6.18.46, commit 1f99e9ab748f)
    builds for an [execveat] relative to a descriptor:

      [if (fd == AT_FDCWD || filename->name[0] == '/')]
        [bprm->filename = filename->name;]
      [else if (filename->name[0] == '\0')]
        [bprm->fdpath = kasprintf(GFP_KERNEL, "/dev/fd/%d", fd);]
      [else]
        [bprm->fdpath = kasprintf(GFP_KERNEL, "/dev/fd/%d/%s", fd, filename->name);]

    The caller's path itself comes through [getname_flags]
    (fs/namei.c), which refuses a name of [PATH_MAX] bytes or more
    counting the NUL (-ENAMETOOLONG), so it is 1 to 4095 bytes, and
    which refuses the EMPTY name with -ENOENT unless the caller passed
    AT_EMPTY_PATH.  With AT_EMPTY_PATH and AT_FDCWD the lookup finds
    the working directory, and [may_open] (fs/namei.c) answers -EACCES
    for a directory opened with MAY_EXEC, so the empty name reaches no
    launch.  A name is NUL-free by construction: [strncpy_from_user]
    stops at the first NUL.

    [fd] is a descriptor number, so it is decimal without a leading
    zero and at most [sysctl_nr_open_max] - 1 = 0x7fffffbf
    (fs/file.c: [sysctl_nr_open_max] is [INT_MAX] masked down to a
    multiple of [BITS_PER_LONG], 0x7fffffc0 on rv64).  The part after [/dev/fd/N/] is the
    caller's own relative name, so it is 1 to 4095 bytes and does not
    start with "/".

    RESIDUAL: a file system limits each NAME COMPONENT — 255 bytes on
    ext4, 1024 on FUSE — and this predicate does not look at
    components.  SCOPE.md records it. *)
Definition byte_is_digit (b : byte) : bool :=
  andb (Z.leb 48 (bv_unsigned b)) (Z.leb (bv_unsigned b) 57).

Definition path_byte : byte := Z_to_bv 8 47.   (* '/' *)

(** A decimal descriptor number: nonempty, every byte a digit, no
    leading zero unless the whole number is "0", and at most
    [sysctl_nr_open_max] - 1. *)
Definition valid_fd_digits (ds : list byte) : Prop :=
  ds <> [] /\ Forall (fun b => byte_is_digit b = true) ds
  /\ (ds = [Z_to_bv 8 48] \/ hd (Z_to_bv 8 48) ds <> Z_to_bv 8 48)
  /\ (Z.of_nat (length ds) <= 10)%Z.

(** A path [getname_flags] can return: 1 to 4095 bytes, no NUL. *)
Definition valid_path_name (p : list byte) : Prop :=
  (1 <= Z.of_nat (length p) <= 4095)%Z /\ ~ In (Z_to_bv 8 0) p.

Definition dev_fd_prefix : list byte :=
  [ Z_to_bv 8 47; Z_to_bv 8 100; Z_to_bv 8 101; Z_to_bv 8 118;
    Z_to_bv 8 47; Z_to_bv 8 102; Z_to_bv 8 100; Z_to_bv 8 47 ].  (* "/dev/fd/" *)

Definition valid_execfn (fn : list byte) : Prop :=
  valid_path_name fn
  \/ (exists ds, fn = dev_fd_prefix ++ ds /\ valid_fd_digits ds)
  \/ (exists ds rest,
        fn = dev_fd_prefix ++ ds ++ [path_byte] ++ rest
        /\ valid_fd_digits ds /\ valid_path_name rest
        /\ hd path_byte rest <> path_byte).

(** ** The joint E2BIG limit

    [bprm_stack_limits] (fs/exec.c) computes

      [limit = _STK_LIM / 4 * 3;]                      (6 MiB)
      [limit = min(limit, bprm->rlim_stack.rlim_cur / 4);]   (2 MiB at the 8 MiB limit)
      [limit = max_t(unsigned long, limit, ARG_MAX);]        (128 KiB)
      [ptr_size = (max(bprm->argc, 1) + bprm->envc) * 8;]
      [if (limit <= ptr_size) return -E2BIG;]
      [limit -= ptr_size;]

    and [bprm_set_stack_limit] records [argmin = bprm->p - limit].
    Every [copy_strings] and [copy_string_kernel] then fails with
    -E2BIG once [bprm->p] falls below [argmin].  [bprm->p] starts at
    the top of the temporary stack and moves down by the file name,
    the envp strings and the argv strings with their NULs, so the
    launch succeeds exactly when those bytes are at most [limit].

    At SCOPE.md's 8 MiB stack limit the first three lines give 2 MiB,
    so the condition is

      [L + 8 * (argc + envc) <= 2 MiB],

    with [L] the string bytes including the NULs.  [valid_argv] admits
    [argc >= 1], so [max(argc, 1)] is [argc].  This is ONE conjunct
    rather than two because [L >= 2] under [valid_execfn], which makes
    the strict [limit > ptr_size] test follow from it.

    [valid_argv]'s own 2 MiB bound and [valid_envp]'s 128 KiB bound
    stay: they are per-list bounds and this is the joint one. *)
Definition e2big_limit : Z := 2097152%Z.

Definition launch_bytes (inp : ProcInput) : Z :=
  (Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))
   + 8 * (Z.of_nat (length (in_argv inp)) + Z.of_nat (length (in_envp inp))))%Z.

Definition valid_launch (inp : ProcInput) : Prop :=
  valid_execfn (in_execfn inp) /\ (launch_bytes inp <= e2big_limit)%Z.

(** * The entry stack image fits inside the user address space

    [init_machine_state] lays [StackLayout.build_stack_bytes] down AT
    AND ABOVE [sp]: argc, the argv and envp pointer arrays, the auxv,
    the argument and environment strings, and the AT_RANDOM block all
    sit at higher addresses than the entry stack pointer.  So a
    placement is one a kernel could have produced only when that whole
    block ends at or below the TOP OF THE USER ADDRESS SPACE the
    declared VA environment provides — [State.sp_window_hi], which is
    riscv64's [STACK_TOP = DEFAULT_MAP_WINDOW = 1 << (MMAP_VA_BITS - 1)]
    = 0x8000_0000_0000 wherever the kernel runs Sv48 or Sv57
    (arch/riscv/include/asm/processor.h [STACK_TOP],
    arch/riscv/include/asm/pgtable.h [MMAP_VA_BITS], Linux v6.18.46,
    commit 1f99e9ab748f; the derivation is in [State.sp_window_hi]'s own
    comment).

    Linux gets this by construction and never has to check it.
    [load_elf_binary] calls [setup_arg_pages] with
    [randomize_stack_top(STACK_TOP)], which returns
    [PAGE_ALIGN(stack_top) - random_variable] and so never exceeds
    [STACK_TOP], which is itself page-aligned (mm/util.c
    [randomize_stack_top]; fs/binfmt_elf.c [load_elf_binary]).  [setup_arg_pages] then sets
    [stack_shift = vma->vm_end - stack_top] and moves [bprm->p] down by
    it (fs/exec.c [setup_arg_pages]), and [create_elf_tables]'s
    [STACK_ADD], [STACK_ROUND] and [STACK_ALLOC] only ever subtract in
    the non-[CONFIG_STACK_GROWSUP] arm (fs/binfmt_elf.c), so the entry
    [sp] sits below everything the kernel wrote and the whole block
    sits at or below [STACK_TOP].  All four at Linux v6.18.46, commit
    1f99e9ab748f.  So [sp + block <= STACK_TOP] holds of every real
    placement.

    The model's block is strictly SMALLER than the kernel's for every
    input, so the premise cannot exclude a placement Linux can produce.
    [StackLayout]'s auxv is 10 entries ([auxv_size] = 160 bytes).
    [create_elf_tables] writes 16 unconditional [NEW_AUX_ENT]s
    (fs/binfmt_elf.c) and then expands riscv's [ARCH_DLINFO], which adds
    [AT_SYSINFO_EHDR] and eight cache-descriptor entries
    (arch/riscv/include/asm/elf.h); it also pushes the [AT_EXECFN]
    pathname string.  Not [AT_PLATFORM]: riscv defines
    [ELF_PLATFORM] as [NULL] (same header), and both the entry and its
    string are under [if (k_platform)], so neither is ever emitted on
    this architecture.  All at Linux v6.18.46, commit 1f99e9ab748f.  The
    premise is therefore LOOSER than the kernel's own ceiling, by a few
    hundred bytes, which costs priority 2 a band of placements no kernel
    produces and costs priority 1 nothing.  This
    model QUANTIFIES [sp] instead of computing it, so the same fact has
    to be a premise or it is not there at all.  Without it the model
    admits entry stacks whose argv/envp strings sit at addresses above
    the last user address: no kernel can produce one, and no user-space
    runtime that holds a picture of the address space (a sanitizer's
    shadow map, a garbage collector's page table) survives being handed
    one, so without it an equivalence statement can be refuted by
    placement alone.

    WHY IT IS STATED PER RUN, coupling the [execve] choice to the
    caller's input.  The block's length depends on argv and envp, which
    arrive in the [State.ProcInput]; [valid_sp] cannot see them, which
    is why this conjunct lives in [valid_entry] and why [valid_entry]
    takes the input.  The alternative — subtracting the WORST-CASE block
    ([entry_stack_span_max], 2238671 bytes) from [sp_window_hi] once and
    for all — stays an absolute window and needs no new argument, but it
    would EXCLUDE real placements: a kernel handed a small argv and envp
    with stack randomization off puts [sp] within a few hundred bytes of
    [STACK_TOP], inside the band the worst case subtracts.  Narrowing
    the quantifier past what a kernel can produce is a soundness hole in
    the equivalence theorem — the excluded runs are real and the theorem
    stops covering them — whereas admitting an impossible placement only
    costs provability.  So the premise is the exact kernel-real
    condition, not the convenient over-approximation of it.

    [entry_stack_span] is an upper bound on the block's length written
    in this file's own vocabulary ([total_arg_bytes]), so [valid_entry]
    and the satisfiability lemmas reason about it without [StackLayout]'s
    layout arithmetic.  What ties it to the real layout is
    [PropExec.build_stack_bytes_within_span], proved where that
    arithmetic lives; [StepTac.bsb_bound] is then derived from the same
    two facts rather than recomputing the sum, so there is one
    derivation and nothing to drift. *)
Definition entry_stack_span (argv envp : list (list byte)) : Z :=
  (8                                    (* argc *)
   + 8 * Z.of_nat (length argv) + 8     (* argv[] and its NULL *)
   + 8 * Z.of_nat (length envp) + 8     (* envp[] and its NULL *)
   + 160                                (* the OLD auxv's size: this
                                           ceiling is a LOWER bound on
                                           Linux's block, kept as the
                                           literal it had while the
                                           model's own auxv was ten
                                           entries, so that the fifth
                                           conjunct of [valid_entry_va]
                                           implies it *)
   + total_arg_bytes argv               (* the argument strings *)
   + total_arg_bytes envp               (* the environment strings *)
   + 7                                  (* 8-alignment padding *)
   + 16)%Z.                             (* the AT_RANDOM block *)

Definition entry_stack_fits (sp : word) (argv envp : list (list byte)) : Prop :=
  (bv_unsigned sp + entry_stack_span argv envp <= sp_window_hi)%Z.

(** The same ceiling under a declared size: [STACK_TOP] is the top of
    the user address space the stack can occupy under every depth, and
    it is [va_stack_top], not [va_task_size], because under Sv57 the two
    differ and the stack sits under the former. *)
Definition entry_stack_fits_va (v : VaSize) (sp : word)
    (argv envp : list (list byte)) : Prop :=
  (bv_unsigned sp + entry_stack_span argv envp <= va_sp_window_hi v)%Z.

Lemma entry_stack_fits_va_sv48 : forall sp argv envp,
  entry_stack_fits_va Sv48 sp argv envp <-> entry_stack_fits sp argv envp.
Proof.
  intros.
  unfold entry_stack_fits_va, entry_stack_fits, va_sp_window_hi, va_stack_top,
    sp_window_hi.
  lia.
Qed.


(** The span of a VALID input is bounded absolutely, by the
    [valid_argv]/[valid_envp] limits.  This is what keeps the new
    conjunct from becoming a second way to empty the entry quantifier
    (the failure mode [image_brk_satisfiable] exists to catch): the
    bottom of the sp window has two gigabytes of room above it and the
    widest admissible block needs 2238671 bytes, so every valid input
    still has a valid entry — [Equivalence.image_brk_satisfiable_entry]
    proves exactly that. *)
Definition entry_stack_span_max : Z := 2238671%Z.

Lemma total_arg_bytes_nonneg : forall args,
  (0 <= total_arg_bytes args)%Z.
Proof.
  induction args as [| a r IH]; unfold total_arg_bytes in *;
    cbn [fold_right] in *; [lia |].
  pose proof (Nat2Z.is_nonneg (length a)). lia.
Qed.

Lemma entry_stack_span_bound : forall argv envp,
  valid_argv argv -> valid_envp envp ->
  (0 <= entry_stack_span argv envp <= entry_stack_span_max)%Z.
Proof.
  intros argv envp [[_ Hla] [Hta _]] [Hle [Hte _]].
  pose proof (total_arg_bytes_nonneg argv).
  pose proof (total_arg_bytes_nonneg envp).
  pose proof (Nat2Z.is_nonneg (length argv)).
  pose proof (Nat2Z.is_nonneg (length envp)).
  unfold entry_stack_span, entry_stack_span_max, auxv_size. lia.
Qed.

(** Validity predicate for an [ExecEntry] — what [execve] may hand this
    binary ON THIS INPUT.  The stack pointer, the program break and the
    mmap base range over their windows (the break's is image-relative,
    hence the [img] argument), and the entry stack image that the
    [execve] choice and the input together determine has to fit below
    the top of the user address space (see [entry_stack_fits] — hence
    the [inp] argument).

    [en_draw] is matched and DISCARDED, deliberately: neither half of
    the draw has a window to lie in, so every value is valid and the
    field contributes no conjunct.  A universal quantifier over valid
    entries therefore ranges over all 2^128 AT_RANDOM draws, and over
    every function the page above the block could hold, with nothing to
    discharge — which is why the field strengthens every
    statement in the tree that quantifies over an entry without changing
    one of their texts.  No ADDRESS moves with the draw either
    ([StackLayout.build_stack_bytes_split_random], carried to the
    mapped image by [PropExec.entry_stack_image_block]), so
    [entry_stack_fits] stays a
    function of (sp, argv, envp) — and it still bounds the whole mapped
    region, page rounding included
    ([PropExec.entry_page_top_within_window]).

    THE WINDOW IS THE DECLARED SIZE'S.  [valid_entry_va] takes the size
    explicitly and [valid_entry] reads it off the input, so a statement
    quantified over [valid_input] -- which pins [Sv48] -- sees exactly
    the Sv48 window ([valid_entry_sv48]), and one quantified
    over an Sv39 input sees the Sv39 window rather than a stack placed
    256 GiB above the last address such a kernel has.  Nothing about the
    run's ANSWERS moves with the size: [run] is the Sv48 run whatever
    the input declares, and [Equivalence.strong_equiv_va] is where a
    statement under another declaration is refused rather than answered
    -- see [State.VaSize] for what the arms implement and for the
    residual. *)
(* =========================================================================
   THE ADMITTED SET: exactly Linux's start states for this launch
   ========================================================================= *)

(** 16-byte and page alignment in [Z], as the kernel's masks work on
    [unsigned long]: [x & ~0xf] and [PAGE_ALIGN(x) = (x + 4095) & ~4095].
    Every address these are applied to is far below 2^64, so the
    wrap-around the C does never happens; the [Z] forms are exact. *)
Definition align_down16 (x : Z) : Z := (x - x mod 16)%Z.

(** [STACK_RND_MASK << PAGE_SHIFT]: the largest stack draw, 0x3ffff
    pages (arch/riscv/include/asm/elf.h, Linux v6.18.46, commit
    1f99e9ab748f, with 4 KiB pages and no compat task). *)
Definition stack_rnd_max : Z := 0x3ffff000%Z.

(** ** Rule 1: the stack VMA's end

    [load_elf_binary] (fs/binfmt_elf.c) calls
    [setup_arg_pages(bprm, randomize_stack_top(STACK_TOP), ...)], and
    [setup_arg_pages] (fs/exec.c) then applies

      [stack_top = arch_align_stack(stack_top);]
      [stack_top = PAGE_ALIGN(stack_top);]

    [randomize_stack_top] (mm/util.c) subtracts [k] pages, [k] from 0
    to 0x3ffff, when PF_RANDOMIZE is set, and nothing otherwise.
    [arch_align_stack] (arch/riscv/kernel/process.c) subtracts [r]
    from 0 to 4095 and clears the low four bits; from a page-aligned
    [T] that gives [T] again for [r] in 0..4094 and [T - 4096] for
    [r = 4095], because [(T - 4095) & ~0xf = T - 4096].  PAGE_ALIGN
    then rounds the first case back up to [T].

    So the end is page-aligned, and it is [T0 - 4096 * k] for [k] in
    [0, 0x40000] with randomization, or [T0] or [T0 - 4096] without.

    WITHOUT RANDOMIZATION THE SECOND PAGE IS STILL LINUX.
    [load_elf_binary] reads [randomize_va_space] ONCE
    ([snapshot_randomize_va_space]) for PF_RANDOMIZE, while
    [arch_align_stack] reads the global again at each of its two
    calls.  A root write to the sysctl during the [execve] therefore
    gives a launch with no stack draw, no base draw, and the
    [arch_align_stack] pad.  Admitting it costs nothing and needs no
    SCOPE.md assumption (dispatch://OSSV-257/ask/a4606aae). *)
Definition valid_stack_top_va (v : VaSize) (aslr : bool) (top : word) : Prop :=
  (bv_unsigned top mod page_size = 0)%Z
  /\ (bv_unsigned top <= va_stack_top v)%Z
  /\ (va_stack_top v
      - (if aslr then stack_rnd_max + page_size else page_size)
      <= bv_unsigned top)%Z.

(** ** Rule 2: the entry stack pointer

    After the strings, [bprm->p] is [top - 8 - L]: the stack VMA's top
    eight bytes are the slot [create_init_stack_vma] (mm/vma_exec.c)
    skipped, and [do_execveat_common] copied [L] bytes of file name,
    envp and argv below it.  [create_elf_tables] (fs/binfmt_elf.c)
    then does

      [p = arch_align_stack(p);]                 (minus 0..4095, then & ~0xf)
      [u_rand_bytes = STACK_ALLOC(p, 16);]       (p -= 16)
      [sp = STACK_ADD(p, ei_index);]             (p - 16 * n_aux)
      [bprm->p = STACK_ROUND(sp, items);]        ((sp - 8 * items) & ~15)

    [p] after [arch_align_stack] is 16-aligned and both 16 and
    [16 * n_aux] are multiples of 16, so the final mask removes exactly
    [8 * (items mod 2)] bytes.  Writing
    [C = 16 + 16 * n_aux + 8 * items + 8 * (items mod 2)]
    ([StackLayout.block_head_size]), the entry stack pointer is

      [sp = align_down16(top - 8 - L - r) - C],   [r] in [0, 4095].

    [align_down16] is monotone and [r] covers a span of 4095, so the
    admitted set is every 16-aligned address in the closed interval
    between the two ends, and nothing else. *)
Definition launch_sp_hi (top : word) (inp : ProcInput) : Z :=
  (align_down16 (bv_unsigned top - 8
                 - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                                 (in_execfn inp)))
   - Z.of_nat (block_head_size (kb_rseq (in_kernel inp))
                               (in_argv inp) (in_envp inp)))%Z.

Definition launch_sp_lo (top : word) (inp : ProcInput) : Z :=
  (align_down16 (bv_unsigned top - 8
                 - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                                 (in_execfn inp))
                 - 4095)
   - Z.of_nat (block_head_size (kb_rseq (in_kernel inp))
                               (in_argv inp) (in_envp inp)))%Z.

Definition valid_launch_sp (top : word) (inp : ProcInput) (sp : word) : Prop :=
  (bv_unsigned sp mod 16 = 0)%Z
  /\ (launch_sp_lo top inp <= bv_unsigned sp <= launch_sp_hi top inp)%Z.

(** ** Rule 3: the mmap base

    [arch_pick_mmap_layout] (mm/util.c) takes
    [random_factor = arch_mmap_rnd()] when PF_RANDOMIZE is set and 0
    otherwise, and calls [mmap_base], which is

      [gap = rlim_stack->rlim_cur;]
      [pad = stack_guard_gap;]
      [if (current->flags & PF_RANDOMIZE) pad += (STACK_RND_MASK << PAGE_SHIFT);]
      [if (gap + pad > gap) gap += pad;]
      [if (gap < MIN_GAP && MIN_GAP < MAX_GAP) gap = MIN_GAP;]
      [else if (gap > MAX_GAP) gap = MAX_GAP;]
      [return PAGE_ALIGN(STACK_TOP - gap - rnd);]

    with [MIN_GAP = SZ_128M] and [MAX_GAP = STACK_TOP / 6 * 5].  The
    [gap + pad > gap] test is the kernel's own overflow guard on
    [unsigned long]; it is written out here rather than simplified
    away, because it is what the source does.

    [arch_mmap_rnd] (mm/util.c) is
    [(get_random_long() & ((1UL << mmap_rnd_bits) - 1)) << PAGE_SHIFT],
    so the draw is [4096 * r] for some [r < 2^mmap_rnd_bits].

    [mmap_is_legacy] is false here: SCOPE.md assumes the top-down
    layout, a finite RLIMIT_STACK and no ADDR_COMPAT_LAYOUT. *)
Definition mmap_min_gap : Z := (128 * 1024 * 1024)%Z.
Definition mmap_max_gap (v : VaSize) : Z := (va_stack_top v / 6 * 5)%Z.

Definition mmap_gap (v : VaSize) (kb : KernelBuild) : Z :=
  let rlim := stack_max_size in
  let pad := (stack_guard_gap_bytes kb
              + if kb_aslr kb then stack_rnd_max else 0)%Z in
  let g := if ((rlim + pad) mod two_pow_64 >? rlim)%Z then (rlim + pad)%Z
           else rlim in
  if andb (g <? mmap_min_gap)%Z (mmap_min_gap <? mmap_max_gap v)%Z
  then mmap_min_gap
  else if (g >? mmap_max_gap v)%Z then mmap_max_gap v else g.

Definition mmap_base_of (v : VaSize) (kb : KernelBuild) (rnd : Z) : Z :=
  page_round_up_Z (va_stack_top v - mmap_gap v kb - rnd).

Definition valid_launch_base (v : VaSize) (kb : KernelBuild) (mbase : word)
    : Prop :=
  exists r : Z,
    (0 <= r)%Z
    /\ (kb_aslr kb = true -> r < 2 ^ mmap_rnd_bits v kb)%Z
    /\ (kb_aslr kb = false -> r = 0%Z)
    /\ bv_unsigned mbase = mmap_base_of v kb (page_size * r).

(** ** The conjunct

    THE START STATE IS EXACTLY A LINUX LAUNCH.  The three rules above
    are the kernel's own steps, so for one input and one
    [State.KernelBuild] the set of (stack top, sp, mmap base) this
    admits is the set a Linux v6.18.46 launch can give, and
    [StackLayout.build_stack_bytes] lays Linux's bytes between sp and
    the top.  There is no band.

    It is a FIFTH conjunct rather than a replacement for the four
    older ones, which it implies, because the tree reads those four
    facts off a destructured entry in thousands of places.  See
    [entry_launch_ok_va_sp], [entry_launch_ok_va_base] and
    [entry_launch_ok_va_fits] for the implications. *)
Definition entry_launch_ok_va (v : VaSize) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  match en with
  | mkEntry sp _ mbase draw =>
    valid_stack_top_va v (kb_aslr (in_kernel inp)) (ed_top draw)
    /\ valid_launch_sp (ed_top draw) inp sp
    /\ valid_launch_base v (in_kernel inp) mbase
  end.

Definition valid_entry_va (v : VaSize) (img : Image) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs _ _, mkEntry sp brk0 mbase _ =>
    valid_sp_va v sp /\ valid_brk segs brk0 /\ valid_mmap_base_va v mbase
    /\ entry_stack_fits_va v sp (in_argv inp) (in_envp inp)
    /\ entry_launch_ok_va v en inp
  end.

Definition valid_entry (img : Image) (en : ExecEntry) (inp : ProcInput) : Prop :=
  valid_entry_va (in_va_size inp) img en inp.

(** The Sv48 instance is the predicate the tree was written against,
    conjunct for conjunct, with the launch conjunct last.  Consumers
    that reason about the window under [valid_input] rewrite with this
    and go on as before. *)
Lemma valid_entry_sv48 : forall img en inp,
  in_va_size inp = Sv48 ->
  (valid_entry img en inp
   <-> match img, en with
       | mkImage segs _ _, mkEntry sp brk0 mbase _ =>
         valid_sp sp /\ valid_brk segs brk0 /\ valid_mmap_base mbase
         /\ entry_stack_fits sp (in_argv inp) (in_envp inp)
         /\ entry_launch_ok_va Sv48 en inp
       end).
Proof.
  intros [segs pc ph] [sp brk0 mbase rnd] inp Hv.
  unfold valid_entry. rewrite Hv. cbn [valid_entry_va].
  rewrite valid_sp_va_sv48, valid_mmap_base_va_sv48, entry_stack_fits_va_sv48.
  reflexivity.
Qed.

(* =========================================================================
   A WITNESS ENTRY FOR EVERY VALID INPUT
   ========================================================================= *)

(** What a vDSO call leaves behind when it leaves nothing behind: the
    caller-saved registers and the frame bytes it found.  A legal
    choice of [StackLayout.ed_vdso] — a vDSO function that writes only
    its result is one Linux can run — and the one a proof that does not
    care about the leftovers names. *)
Definition vdso_keeps_all
    : nat -> list word -> list byte -> word -> (list word * list byte) :=
  fun _ regs frame _ => (regs, frame).

(** THE WITNESS ENTRY, and the lemma that makes repairing a consumer
    cheap.

    A proof that used to write

      [exists (mkEntry sp brk base (mkDraw rnd slack)). ... ]

    and discharge four conjuncts by [lia] now writes

      [exists (launch_entry_va v inp brk rnd vdso_keeps_all).]
      [apply launch_entry_va_valid; ...]

    and discharges the launch conjunct by the lemma rather than by
    arithmetic.  The witness is the one the spec names: the stack at
    the very top ([ed_top = STACK_TOP], the launch with no stack
    draw), the stack pointer at the top of rule 2 (the launch with no
    [arch_align_stack] pad), and the mmap base of rule 3 with the draw
    at 0.  That triple is a Linux launch for every valid input and
    every kernel build, under all three address-space sizes.

    [brk] stays an argument: it is a fact about the IMAGE's
    reservations, which this file does not compute
    ([Equivalence.image_brk_witness] does). *)
Definition launch_entry_va (v : VaSize) (inp : ProcInput) (brk : word)
    (rnd : bv 128)
    (vd : nat -> list word -> list byte -> word -> (list word * list byte))
    : ExecEntry :=
  let top := Z_to_bv 64 (va_stack_top v) in
  mkEntry (Z_to_bv 64 (launch_sp_hi top inp))
          brk
          (Z_to_bv 64 (mmap_base_of v (in_kernel inp) 0))
          (mkDraw rnd top vd).

(* ------------------------------------------------------------------
   THE ARITHMETIC OF THE FIFTH CONJUNCT

   The kernel's three masks -- [PAGE_ALIGN], [x & ~0xf] and the gap
   clamp in [mmap_base] (mm/util.c, Linux v6.18.46, commit
   1f99e9ab748f) -- as inequalities, once.  Every bound below is a
   closed bound on a huge literal, so each division is turned into an
   inequality here and no later goal reaches [lia] with one still in
   it.
   ------------------------------------------------------------------ *)

Lemma launch_page_round_up_ge : forall z, (z <= page_round_up_Z z)%Z.
Proof.
  intros z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(discriminate)).
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)).
  lia.
Qed.

Lemma launch_page_round_up_lt : forall z, (page_round_up_Z z < z + page_size)%Z.
Proof.
  intros z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(discriminate)).
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)).
  lia.
Qed.

(** [PAGE_ALIGN] reaches no further than the first page boundary at or
    above its argument, so a page-aligned ceiling survives it. *)
Lemma launch_page_round_up_le : forall z b,
  (z <= b)%Z -> (b mod page_size = 0)%Z -> (page_round_up_Z z <= b)%Z.
Proof.
  intros z b Hzb Hb. unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(discriminate)).
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)).
  pose proof (Z.div_mod b 4096 ltac:(discriminate)).
  lia.
Qed.

Lemma launch_page_round_up_mod : forall z,
  (page_round_up_Z z mod page_size = 0)%Z.
Proof. intros z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma align_down16_le : forall x, (align_down16 x <= x)%Z.
Proof.
  intros x. unfold align_down16.
  pose proof (Z.mod_pos_bound x 16 ltac:(lia)). lia.
Qed.

Lemma align_down16_ge : forall x, (x - 15 <= align_down16 x)%Z.
Proof.
  intros x. unfold align_down16.
  pose proof (Z.mod_pos_bound x 16 ltac:(lia)). lia.
Qed.

(** Why rule 2 ranges over a closed INTERVAL rather than a scattered
    set: [arch_align_stack] subtracts 0 to 4095 and then masks, and the
    mask is monotone. *)
Lemma align_down16_mono : forall x y,
  (x <= y)%Z -> (align_down16 x <= align_down16 y)%Z.
Proof.
  intros x y Hxy. unfold align_down16.
  pose proof (Z.div_mod x 16 ltac:(discriminate)).
  pose proof (Z.div_mod y 16 ltac:(discriminate)).
  pose proof (Z.mod_pos_bound x 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
  lia.
Qed.

Lemma align_down16_mod16 : forall x, (align_down16 x mod 16 = 0)%Z.
Proof.
  intros x. unfold align_down16.
  pose proof (Z.div_mod x 16 ltac:(discriminate)).
  replace (x - x mod 16)%Z with (16 * (x / 16))%Z by lia.
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(** C, the head of the block, in this file's own vocabulary: it moves
    with the two pointer arrays and with nothing else, because
    [StackLayout.auxv_count] is 27 or 29 and [STACK_ROUND] adds at most
    one eight-byte word. *)
Lemma block_head_size_bounds : forall rseq argv envp,
  (8 * (Z.of_nat (length argv) + Z.of_nat (length envp)) + 472
   <= Z.of_nat (block_head_size rseq argv envp)
   <= 8 * (Z.of_nat (length argv) + Z.of_nat (length envp)) + 512)%Z.
Proof.
  intros rseq argv envp.
  unfold block_head_size, block_items, auxv_size, auxv_count.
  assert (Hm : (Nat.modulo (length argv + length envp + 3) 2 < 2)%nat)
    by (apply Nat.mod_upper_bound; discriminate).
  destruct rseq; lia.
Qed.

(** C is a multiple of 16, which is why [STACK_ROUND]'s result is: the
    [8 * items] of the pointer arrays and the [8 * (items mod 2)] the
    mask removes always pair up. *)
Lemma block_head_size_mod16 : forall rseq argv envp,
  (Z.of_nat (block_head_size rseq argv envp) mod 16 = 0)%Z.
Proof.
  intros rseq argv envp.
  assert (Hk : exists k, block_head_size rseq argv envp = (16 * k)%nat).
  { unfold block_head_size, block_items, auxv_size, auxv_count.
    exists (((length argv + length envp + 3) / 2)
            + ((length argv + length envp + 3) mod 2)
            + (if rseq then 29 else 27) + 1)%nat.
    pose proof (Nat.div_mod_eq (length argv + length envp + 3) 2).
    destruct rseq; lia. }
  destruct Hk as [k Hk]. rewrite Hk, Nat2Z.inj_mul.
  change (Z.of_nat 16) with 16%Z. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(** The strings [copy_strings] (fs/exec.c) copied, counted twice over:
    [StackLayout.flatten_strings] lays each string and its NUL, which
    is what [total_arg_bytes] sums. *)
Lemma length_flatten_strings : forall l,
  Z.of_nat (length (flatten_strings l)) = total_arg_bytes l.
Proof.
  induction l as [|a l IH]; [reflexivity|].
  unfold flatten_strings, total_arg_bytes in *.
  cbn [flat_map fold_right]. rewrite !length_app. cbn [length]. lia.
Qed.

Lemma launch_string_bytes_ge : forall argv envp execfn,
  (total_arg_bytes argv + total_arg_bytes envp + 1
   <= Z.of_nat (launch_string_bytes argv envp execfn))%Z.
Proof.
  intros argv envp execfn. unfold launch_string_bytes.
  pose proof (length_flatten_strings argv).
  pose proof (length_flatten_strings envp).
  pose proof (Nat2Z.is_nonneg (length execfn)).
  lia.
Qed.

(** [mmap_base]'s clamp, with the gap abstracted: whatever the
    unclamped gap is, the result lies between MIN_GAP and MAX_GAP, and
    it never exceeds the larger of MIN_GAP and the unclamped gap. *)
Lemma launch_clamp_facts : forall g lo hi : Z,
  (lo < hi)%Z ->
  (lo <= (if (g <? lo)%Z && (lo <? hi)%Z then lo
          else if (g >? hi)%Z then hi else g) <= hi)%Z
  /\ ((if (g <? lo)%Z && (lo <? hi)%Z then lo
       else if (g >? hi)%Z then hi else g) <= Z.max lo g)%Z.
Proof.
  intros g lo hi Hlh.
  destruct ((g <? lo)%Z && (lo <? hi)%Z) eqn:E1.
  - split; lia.
  - apply andb_false_iff in E1 as [E1 | E1]; apply Z.ltb_ge in E1; [| exfalso; lia].
    destruct ((g >? hi)%Z) eqn:E2.
    + apply Z.gtb_lt in E2. split; lia.
    + rewrite Z.gtb_ltb in E2. apply Z.ltb_ge in E2. split; lia.
Qed.

Lemma mmap_gap_bounds : forall v kb,
  (mmap_min_gap <= mmap_gap v kb <= mmap_max_gap v)%Z
  /\ (mmap_gap v kb
      <= Z.max mmap_min_gap
               (stack_max_size + stack_guard_gap_bytes kb + stack_rnd_max))%Z.
Proof.
  intros v kb.
  assert (Hmm : (mmap_min_gap < mmap_max_gap v)%Z)
    by (destruct v; vm_compute; reflexivity).
  pose proof (stack_guard_gap_bytes_bounds kb) as Hguard.
  unfold mmap_gap. cbv zeta.
  set (pad := (stack_guard_gap_bytes kb
               + (if kb_aslr kb then stack_rnd_max else 0))%Z).
  assert (Hpad : (0 <= pad <= stack_guard_gap_bytes kb + stack_rnd_max)%Z)
    by (unfold pad; destruct (kb_aslr kb); unfold stack_rnd_max; lia).
  set (g := (if ((stack_max_size + pad) mod two_pow_64 >? stack_max_size)%Z
             then (stack_max_size + pad)%Z else stack_max_size)).
  assert (Hgle : (g <= stack_max_size + pad)%Z).
  { unfold g.
    destruct ((stack_max_size + pad) mod two_pow_64 >? stack_max_size)%Z;
      unfold stack_max_size; lia. }
  destruct (launch_clamp_facts g mmap_min_gap (mmap_max_gap v) Hmm) as [Hb Hc].
  split; [exact Hb |]. unfold stack_max_size in *. lia.
Qed.

(* ------------------------------------------------------------------
   THE FOUR OLDER CONJUNCTS ARE CONSEQUENCES OF THE FIFTH
   ------------------------------------------------------------------ *)

(** [valid_sp_va] from the launch conjunct.  [valid_launch] is a real
    premise and the only one: it is the E2BIG cap, and it bounds the
    strings AND the pointer arrays jointly, so [valid_argv] and
    [valid_envp] add nothing here.  Without a cap the block could reach
    below the bottom of the sp window. *)
Lemma entry_launch_ok_va_sp : forall v en inp,
  valid_launch inp -> entry_launch_ok_va v en inp -> valid_sp_va v (en_sp en).
Proof.
  intros v [sp brk0 mbase draw] inp [_ Hlb] Hok.
  cbn [en_sp] in *. cbn [entry_launch_ok_va] in Hok.
  destruct Hok as [Htop [Hsp _]].
  unfold valid_stack_top_va in Htop. destruct Htop as [_ [Htople Htopge]].
  unfold valid_launch_sp in Hsp. destruct Hsp as [Hspmod [Hsplo Hsphi]].
  unfold launch_bytes in Hlb.
  pose proof (block_head_size_bounds (kb_rseq (in_kernel inp))
                (in_argv inp) (in_envp inp)) as [HCl HCh].
  pose proof (launch_string_bytes_ge (in_argv inp) (in_envp inp)
                (in_execfn inp)) as HL.
  pose proof (total_arg_bytes_nonneg (in_argv inp)).
  pose proof (total_arg_bytes_nonneg (in_envp inp)).
  pose proof (Nat2Z.is_nonneg (length (in_argv inp))).
  pose proof (Nat2Z.is_nonneg (length (in_envp inp))).
  unfold launch_sp_hi in Hsphi. unfold launch_sp_lo in Hsplo.
  pose proof (align_down16_le
    (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp)))) as Hal1.
  pose proof (align_down16_ge
    (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp)) - 4095)) as Hal2.
  unfold valid_sp_va, va_sp_window_lo, va_sp_window_hi, e2big_limit in *.
  split; [| split; [| exact Hspmod]].
  - destruct (kb_aslr (in_kernel inp));
      unfold stack_rnd_max, page_size in *; lia.
  - lia.
Qed.

(** [entry_stack_fits_va] from the launch conjunct, with the same
    premise: [entry_stack_span] counts the pointer arrays, the strings,
    a 160-byte auxv and 31 bytes of slack, and the real block's
    [8 + L + C] is larger term for term. *)
Lemma entry_launch_ok_va_fits : forall v en inp,
  valid_launch inp -> entry_launch_ok_va v en inp ->
  entry_stack_fits_va v (en_sp en) (in_argv inp) (in_envp inp).
Proof.
  intros v [sp brk0 mbase draw] inp [_ Hlb] Hok.
  cbn [en_sp] in *. cbn [entry_launch_ok_va] in Hok.
  destruct Hok as [Htop [Hsp _]].
  unfold valid_stack_top_va in Htop. destruct Htop as [_ [Htople _]].
  unfold valid_launch_sp in Hsp. destruct Hsp as [_ [_ Hsphi]].
  pose proof (block_head_size_bounds (kb_rseq (in_kernel inp))
                (in_argv inp) (in_envp inp)) as [HCl _].
  pose proof (launch_string_bytes_ge (in_argv inp) (in_envp inp)
                (in_execfn inp)) as HL.
  unfold launch_sp_hi in Hsphi.
  pose proof (align_down16_le
    (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp)))) as Hal1.
  unfold entry_stack_fits_va, entry_stack_span, va_sp_window_hi in *. lia.
Qed.

(** [valid_mmap_base_va] from the launch conjunct, with no premise at
    all: rule 3 pins the base to [PAGE_ALIGN(STACK_TOP - gap - rnd)],
    the gap is at least MIN_GAP, and [State.stack_guard_gap_bytes]
    together with [State.mmap_rnd_bits_max] keeps the base at or above
    [State.mmap_base_min] under Sv48 and Sv57.  Under Sv39 the clamp at
    MAX_GAP can fire and the kernel's own subtraction can pass zero, so
    the floor there is zero, which every address meets. *)
Lemma entry_launch_ok_va_base : forall v en inp,
  entry_launch_ok_va v en inp -> valid_mmap_base_va v (en_mmap_base en).
Proof.
  intros v [sp brk0 mbase draw] inp Hok.
  cbn [en_mmap_base] in *. cbn [entry_launch_ok_va] in Hok.
  destruct Hok as [_ [_ Hbase]].
  unfold valid_launch_base in Hbase.
  destruct Hbase as [r [Hr0 [Hrt [Hrf Heq]]]].
  pose proof (mmap_gap_bounds v (in_kernel inp)) as [[Hgl _] Hgmax].
  pose proof (stack_guard_gap_bytes_bounds (in_kernel inp)) as Hguard.
  pose proof (bv_unsigned_in_range 64 mbase) as Hmr.
  assert (Hrb : (page_size * r <= 35184372084736)%Z).
  { destruct (kb_aslr (in_kernel inp)).
    - pose proof (mmap_rnd_bits_bounds v (in_kernel inp)) as [_ Hb].
      assert (Hmax : (mmap_rnd_bits_max v <= 33)%Z)
        by (destruct v; cbn; lia).
      assert (Hp : (2 ^ mmap_rnd_bits v (in_kernel inp) <= 8589934592)%Z).
      { replace 8589934592%Z with (2 ^ 33)%Z by (vm_compute; reflexivity).
        apply Z.pow_le_mono_r; lia. }
      pose proof (Hrt eq_refl). unfold page_size. lia.
    - rewrite (Hrf eq_refl). unfold page_size. lia. }
  split; [| split].
  - destruct v.
    + (* Sv39: no address is below zero *)
      unfold va_mmap_base_min. lia.
    + rewrite Heq. unfold mmap_base_of.
      eapply Z.le_trans; [| apply launch_page_round_up_ge].
      unfold va_mmap_base_min, mmap_base_min, va_stack_top, sp_window_hi,
        mmap_min_gap, stack_max_size, stack_rnd_max, page_size in *. lia.
    + rewrite Heq. unfold mmap_base_of.
      eapply Z.le_trans; [| apply launch_page_round_up_ge].
      unfold va_mmap_base_min, mmap_base_min, va_stack_top, sp_window_hi,
        mmap_min_gap, stack_max_size, stack_rnd_max, page_size in *. lia.
  - rewrite Heq. unfold mmap_base_of. apply launch_page_round_up_le.
    + unfold va_mmap_base_max, mmap_min_gap, page_size in *. lia.
    + destruct v; vm_compute; reflexivity.
  - rewrite Heq. unfold mmap_base_of. apply launch_page_round_up_mod.
Qed.

(* ------------------------------------------------------------------
   THE WITNESS SATISFIES THE LAUNCH CONJUNCT
   ------------------------------------------------------------------ *)

Lemma launch_top_unsigned : forall v,
  bv_unsigned (Z_to_bv 64 (va_stack_top v)) = va_stack_top v.
Proof.
  intros v. apply bv_unsigned_Z_to_bv_u64.
  destruct v; unfold va_stack_top, sv39_task_size, sp_window_hi, two_pow_64;
    split; [lia | vm_compute; reflexivity | lia | vm_compute; reflexivity
           | lia | vm_compute; reflexivity].
Qed.

(** The witness stack pointer is a real address: the block below
    STACK_TOP is at most [8 + 4095 + 15] bytes of masks plus the E2BIG
    cap plus C, far less than the 2^38 of the smallest STACK_TOP. *)
Lemma launch_sp_hi_range : forall v inp,
  valid_launch inp ->
  (0 < launch_sp_hi (Z_to_bv 64 (va_stack_top v)) inp < two_pow_64)%Z.
Proof.
  intros v inp [_ Hlb]. unfold launch_bytes in Hlb.
  unfold launch_sp_hi. rewrite launch_top_unsigned.
  pose proof (block_head_size_bounds (kb_rseq (in_kernel inp))
                (in_argv inp) (in_envp inp)) as [HCl HCh].
  pose proof (launch_string_bytes_ge (in_argv inp) (in_envp inp)
                (in_execfn inp)) as HL.
  pose proof (total_arg_bytes_nonneg (in_argv inp)).
  pose proof (total_arg_bytes_nonneg (in_envp inp)).
  pose proof (Nat2Z.is_nonneg (length (in_argv inp))).
  pose proof (Nat2Z.is_nonneg (length (in_envp inp))).
  pose proof (align_down16_le
    (va_stack_top v - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp)))) as Hal1.
  pose proof (align_down16_ge
    (va_stack_top v - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp)))) as Hal2.
  assert (H64 : two_pow_64 = 18446744073709551616%Z)
    by (vm_compute; reflexivity).
  unfold e2big_limit in *. rewrite H64.
  destruct v; unfold va_stack_top, sv39_task_size, sp_window_hi in *; lia.
Qed.

(** The witness mmap base is a real address too: the gap is at most
    MAX_GAP = [STACK_TOP / 6 * 5], so with the draw at 0 the base stays
    a sixth of the address space above zero. *)
Lemma launch_mmap_base_range : forall v kb,
  (0 < mmap_base_of v kb 0 < two_pow_64)%Z.
Proof.
  intros v kb.
  pose proof (mmap_gap_bounds v kb) as [[Hgl Hgh] _].
  pose proof (launch_page_round_up_ge (va_stack_top v - mmap_gap v kb - 0)) as H1.
  pose proof (launch_page_round_up_lt (va_stack_top v - mmap_gap v kb - 0)) as H2.
  assert (H64 : two_pow_64 = 18446744073709551616%Z)
    by (vm_compute; reflexivity).
  unfold mmap_base_of. rewrite H64.
  destruct v;
    [ assert (Hmg : mmap_max_gap Sv39 = 229064922450%Z)
        by (vm_compute; reflexivity)
    | assert (Hmg : mmap_max_gap Sv48 = 117281240296105%Z)
        by (vm_compute; reflexivity)
    | assert (Hmg : mmap_max_gap Sv57 = 117281240296105%Z)
        by (vm_compute; reflexivity) ];
    rewrite Hmg in Hgh;
    unfold va_stack_top, sv39_task_size, sp_window_hi, mmap_min_gap,
      page_size in *; lia.
Qed.

(** THE WITNESS IS A LINUX LAUNCH.  The stack at the very top (the
    launch with no stack draw), the stack pointer at the top of rule 2
    (no [arch_align_stack] pad), the mmap base of rule 3 with the draw
    at 0.  [valid_launch] is what makes [sp] an address at all. *)
Lemma launch_entry_va_launch_ok : forall v inp brk rnd vd,
  valid_launch inp ->
  entry_launch_ok_va v (launch_entry_va v inp brk rnd vd) inp.
Proof.
  intros v inp brk rnd vd Hl.
  pose proof (launch_top_unsigned v) as Htop.
  pose proof (launch_sp_hi_range v inp Hl) as Hspr.
  cbn [launch_entry_va entry_launch_ok_va ed_top].
  split; [| split].
  - unfold valid_stack_top_va. rewrite Htop.
    split; [destruct v; vm_compute; reflexivity |].
    split; [lia |].
    destruct (kb_aslr (in_kernel inp)); unfold stack_rnd_max, page_size; lia.
  - unfold valid_launch_sp.
    assert (Hu : bv_unsigned
                   (Z_to_bv 64 (launch_sp_hi (Z_to_bv 64 (va_stack_top v)) inp))
                 = launch_sp_hi (Z_to_bv 64 (va_stack_top v)) inp)
      by (apply bv_unsigned_Z_to_bv_u64; lia).
    rewrite Hu. split; [| split; [| lia]].
    + unfold launch_sp_hi.
      rewrite Zminus_mod, align_down16_mod16, block_head_size_mod16.
      reflexivity.
    + unfold launch_sp_lo, launch_sp_hi.
      pose proof (align_down16_mono
        (bv_unsigned (Z_to_bv 64 (va_stack_top v)) - 8
         - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                         (in_execfn inp)) - 4095)
        (bv_unsigned (Z_to_bv 64 (va_stack_top v)) - 8
         - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                         (in_execfn inp)))
        ltac:(lia)).
      lia.
  - unfold valid_launch_base. exists 0%Z.
    split; [lia |].
    split.
    + intros _. pose proof (mmap_rnd_bits_bounds v (in_kernel inp)) as [Hb _].
      apply Z.pow_pos_nonneg; lia.
    + split; [intros _; reflexivity |].
      rewrite Z.mul_0_r. apply bv_unsigned_Z_to_bv_u64.
      pose proof (launch_mmap_base_range v (in_kernel inp)). lia.
Qed.

(** THE WITNESS, in one lemma.  The launch conjunct is proved directly
    and the four older ones are read off it by the three implications
    above, so there is one piece of arithmetic and not five.

    [valid_argv] and [valid_envp] are premises because the statement is
    the one every consumer has: the proof needs only [valid_launch],
    whose E2BIG cap bounds the strings and the pointer arrays together.
    [brk] stays an argument, a fact about the image's reservations. *)
Lemma launch_entry_va_valid : forall v segs pc ph inp brk rnd vd,
  valid_argv (in_argv inp) ->
  valid_envp (in_envp inp) ->
  valid_launch inp ->
  valid_brk segs brk ->
  valid_entry_va v (mkImage segs pc ph) (launch_entry_va v inp brk rnd vd) inp.
Proof.
  intros v segs pc ph inp brk rnd vd Ha He Hl Hbrk.
  pose proof (launch_entry_va_launch_ok v inp brk rnd vd Hl) as Hok.
  cbn [valid_entry_va launch_entry_va].
  split; [| split; [| split; [| split]]].
  - exact (entry_launch_ok_va_sp v (launch_entry_va v inp brk rnd vd) inp Hl Hok).
  - exact Hbrk.
  - exact (entry_launch_ok_va_base v (launch_entry_va v inp brk rnd vd) inp Hok).
  - exact (entry_launch_ok_va_fits v (launch_entry_va v inp brk rnd vd) inp Hl Hok).
  - exact Hok.
Qed.

(** Validity predicate for the user and group a process is launched as
    — the credential half of a [State.ProcInput], and the model's answer
    to "which user is this?" in the same sense [valid_sp] and
    [valid_brk] are its answer to "where is the stack?": a window the
    environment chooses from, not a value the model invents.

    An id is a 32-BIT value.  Every credential syscall declares its
    arguments [uid_t]/[gid_t], so the kernel never sees more than 32
    bits of one (see [Syscall.uid32]), and a process whose real id did
    not fit would be one no [getuid] could report.

    [(uid_t)-1] is EXCLUDED.  [make_kuid] maps it to [INVALID_UID]
    (Linux v6.18.46, commit 1f99e9ab748f, kernel/user_namespace.c,
    [make_kuid] — byte-identical there and at every mainline release tag
    from v6.10 through v6.18 — via the [KUIDT_INIT(-1)] sentinel
    [INVALID_UID] in include/linux/uidgid.h),
    which every id-setting path rejects with -EINVAL, so no process can
    hold it and no [execve] can produce one.  The model excludes it here
    rather than leaving [Kernel.Sys.setid_spec] to answer a state that
    cannot arise.

    WHAT THIS PREDICATE DOES NOT COVER, and does not need to: a
    SECURE-EXEC.  That is excluded by CONSTRUCTION rather than by a
    clause here — [State.ProcInput] has no effective-id field, so
    [State.init_model] derives the effective and saved ids from the real
    ones, and a launch whose effective id differs cannot be stated.  A
    set-user-id or set-group-id binary, or one carrying file
    capabilities, starts with an effective id that differs from its real
    one, and libc then takes its secure-exec path — musl's [__init_libc]
    computes [libc.secure] from exactly that inequality and from
    [AT_SECURE], and the path probes and sanitizes fds 0-2 with syscalls
    outside [Specs.modeled_sysnos].  Admitting such a launch would make
    the model claim behavior for a startup it does not cover, so it is
    excluded here and [State.init_model] gives every run real, effective
    and saved ids that agree.  [StackLayout.auxv_entries] states the same
    restriction from the other side, as the reason its [AT_SECURE] is 0. *)
Definition valid_id (u : word) : Prop :=
  (bv_unsigned u < 2 ^ 32 - 1)%Z.

Definition valid_creds (inp : ProcInput) : Prop :=
  valid_id (in_uid inp) /\ valid_id (in_gid inp).

(** The soft RLIMIT_NOFILE a launch can really carry.  [do_prlimit]
    enforces [rlim_cur <= rlim_max] and refuses a NOFILE [rlim_max] above
    the live [sysctl_nr_open] (kernel/sys.c, Linux v6.18.46, commit
    1f99e9ab748f), and it is the only writer that a running process can
    reach for this resource.  Not the only writer of the ARRAY, which is
    a weaker and more useful fact, because the others are all at exec or
    boot: [setup_new_exec] writes [RLIMIT_STACK] (fs/exec.c),
    [do_coredump] writes [RLIMIT_CORE] (fs/coredump.c), [acct_pin_kill]
    writes [RLIMIT_FSIZE] (kernel/acct.c), [fork_init] writes
    [init_task]'s NPROC and SIGPENDING (kernel/fork.c), and the LSM
    [bprm_committing_creds] hooks -- SELinux's
    [selinux_bprm_committing_creds] and AppArmor's -- loop over ALL of
    [RLIM_NLIMITS], NOFILE included, clamping each soft limit to
    [min(rlim_max, init_task's soft)] on a domain transition.  That last
    one is the reason this bound is a property of the LAUNCH rather than
    of the model: an LSM clamp has already happened by the time the run
    starts, and the field records where it landed.

    [sysctl_nr_open] is itself bounded by [sysctl_nr_open_max], the
    smaller of INT_MAX and the pointer-sized division
    [~(size_t)0 / sizeof a pointer], rounded down to a multiple of
    BITS_PER_LONG -- 2^31 - 64 on LP64 (fs/file.c, wired as the
    [proc_douintvec_minmax] ceiling in fs/file_table.c).  That divisor is
    PARAPHRASED rather than quoted, and the reason is worth a line
    because it cost two builds: the kernel writes the divisor as a
    [sizeof] of a pointer type, which in C ends with a star and then a
    close paren -- and those two characters END A ROCQ COMMENT.  Quoting
    the C spelling therefore terminates this comment in the middle of a
    sentence, and the file goes on to fail at whatever vernacular the
    remaining prose runs into, hundreds of lines below, naming a place
    with nothing wrong with it.  Paraphrase any C fragment whose last
    two characters are those.
    [INIT_RLIMITS] starts the init task at 1024 and fork copies an
    already-valid pair, so no live [rlim_cur] exceeds that bound.
    RLIM_INFINITY least of all: it is above [sysctl_nr_open] by
    construction, which is why this one resource has no unlimited
    case.

    A CLAUSE RATHER THAN SLACK.  [Fs.File.dup3_spec] reads this limit and
    ANSWERS from it — it does not decline on it, the way
    [Kernel.Groups.getgroups_spec] declines an over-long [in_groups] — so
    a larger range would not be extra coverage but extra IMPOSSIBLE
    traces, concretely answered.  What the clause does NOT carry is the
    soundness of the returned fd: that rests on the two success arms'
    own bounds, since the extracted checker is handed a model directly
    and never sees this predicate. *)
Definition valid_nofile (n : word) : Prop :=
  (bv_unsigned n <= 2 ^ 31 - 64)%Z.

(** The blocked mask a process can be STARTED with.  SIGKILL and SIGSTOP
    are never in it, and the clause is here rather than in the spec
    because it is a property of how the process was launched: nothing
    [Kernel.Signal.rt_sigprocmask_spec] does can introduce those bits,
    so if they are absent on entry they are absent for the whole run.

    WHY IT HOLDS, AS AN ENUMERATION AND NOT AS A ONE-LINER.  The tempting
    reason — "every path that installs a mask strips them" — is FALSE,
    and kernel/signal.c says so directly above [sigprocmask]: "Unlike the
    user-mode sys_sigprocmask(), the kernel interface happily blocks
    'unblockable' signals like SIGKILL and friends."  What is true is
    that every path leaving a mask on a task that then RETURNS TO
    USERSPACE either strips the two bits or cannot set them (Linux
    v6.18.46, commit 1f99e9ab748f):

      - [SYSCALL_DEFINE4(rt_sigprocmask)] strips [new_set] itself,
        before calling [sigprocmask] (kernel/signal.c);
      - [set_current_blocked] strips, and it is what [set_user_sigmask]
        (ppoll, pselect6, epoll_pwait, io_pgetevents, io_uring_enter),
        [sigsuspend], sigreturn and handler setup all go through
        (kernel/signal.c);
      - [ptrace_setsigmask] strips (kernel/ptrace.c);
      - [force_sig_info_to_task] and [do_sigtimedwait] only CLEAR bits
        (kernel/signal.c);
      - PID 1 starts from [init_task]'s zeroed [.blocked]
        (init/init_task.c) and execve preserves whatever it inherits —
        [fs/exec.c] never names [blocked] — so the property is
        inductive along the whole process tree;
      - two writers assign [current->blocked] DIRECTLY, reaching neither
        strip.  fs/coda/upcall.c's [coda_block_signals] is [sigfillset]
        then [sigdelset] of SIGKILL, SIGSTOP and SIGINT, so it clears
        both bits itself and this conclusion survives it rather than
        resting on it ([coda_unblock_signals] puts the saved set back);
        drivers/isdn/mISDN/stack.c's [mISDNStackd] does
        [sigfillset(&current->blocked)] with no strip at all, and is a
        kthread that never returns to userspace, so it is outside what
        this list quantifies over.  security/selinux/hooks.c's
        [selinux_bprm_committed_creds] only [sigemptyset]s;
      - the in-kernel [sigprocmask] windows that genuinely do set the
        two bits are THREE [sigfillset]s, and they are not all
        filesystem operations: [ocfs2_block_signals] (fs/ocfs2/super.c)
        and [__smb_send_rqst] (fs/smb/client/transport.c) are, and
        [ab8500_power_off] (drivers/mfd/ab8500-sysctrl.c) is a power-off
        path.  What they share is not the subsystem but the shape — the
        mask is restored on the next line or two, before the task can
        execute another syscall.  fs/ceph/addr.c's [ceph_block_sigs]
        blocks everything but SIGKILL, so it sets one of the two bits,
        and restores the same way.

    IT IS AN ABSENCE ARGUMENT, so it rots the way absence arguments do:
    a future kernel that leaves either bit set on a task returning to
    userspace falsifies it.  The direction is safe — a clause here only
    NARROWS the environments the theorem speaks about, and can never
    make the model admit an answer Linux would not give — but a
    narrowed theorem is a weaker one, so the clause is worth deleting if
    it stops being true rather than working around.

    WHY IT IS WORTH STATING AT ALL, given that omitting it would be
    sound: [Kernel.Signal.rt_sigprocmask_spec] copies the entry mask
    back out through [oset] verbatim, so without this clause the model
    would admit a program that reads [oset], finds SIGKILL blocked, and
    branches on it — a trace no Linux process has.  That is the
    second of this development's three priorities. *)
Definition valid_sigmask (inp : ProcInput) : Prop :=
  bv_and (in_sigmask inp) (Z_to_bv 64 sig_kernel_only_mask) = Z_to_bv 64 0.

(** Validity predicate for the AT_HWCAP word the auxv publishes — the
    model's answer to "which hart is this?" in the same sense
    [valid_sp] is its answer to "where is the stack?": a set the
    environment chooses from, not a value the model invents.

    Exactly two words, and the argument that it is exactly these two is
    in [StackLayout]'s AT_HWCAP bullet, which reads it out of the
    kernel source.  In outline: [riscv_get_elf_hwcap] masks the published word
    down to the single-letter extension bits
    (arch/riscv/kernel/cpufeature.c:1108, [RISCV_ISA_EXT_BASE] = 26 in
    arch/riscv/include/asm/hwcap.h:33) and [riscv_fill_hwcap] can only
    ever set seven of them — i m a f d c v
    (arch/riscv/kernel/cpufeature.c:1059-1065, Linux v6.18.46, commit
    1f99e9ab748f) — so the architecture's whole range is the subsets of
    {A,C,D,F,I,M,V}.  Six of those bits are then fixed by the ISA this
    model EXECUTES ([Riscv.Decode] is RV64IMAFD, [Riscv.DecodeC] adds
    C): a hart missing one of them would not run the instructions the
    semantics interprets at all.  The seventh, V, is free, because
    [RiscvSemantics.decode_exec_accesses] answers a word it cannot
    decode with [MachineUnmodeled] rather than a trap — the model does
    not claim the hart lacks V, so it must not publish a word that says
    so — and because the kernel produces both masks on one
    machine, clearing V whenever
    [riscv_v_vstate_ctrl_user_allowed()] is false
    (arch/riscv/kernel/cpufeature.c:1114-1115), which a process controls
    through [PR_RISCV_V_SET_CONTROL].

    UNLIKE the other clauses of [valid_input], this one WIDENS what the
    theorem must survive rather than narrowing it: an auxv with no
    AT_HWCAP entry at all is a vector
    no v6.18.46 kernel builds ([create_elf_tables] emits the entry
    unconditionally, fs/binfmt_elf.c:249).  A binary whose runtime
    dispatches on the V bit has to be equivalent under BOTH masks,
    and under [hwcap_rv64gcv] its vector path is a word the decoder
    returns [None] for, so the run is [MachineUnmodeled].  That is the
    intended consequence: such a binary leaves the modeled surface
    instead of being proved to take a scalar path a real process would
    not have taken. *)
Definition valid_hwcap (h : word) : Prop :=
  h = hwcap_rv64gc \/ h = hwcap_rv64gcv.

(** THE RANDOM DEVICE'S DECLARED STREAM NEVER ENDS.

    THIS IS THE ONE CLAUSE HERE THAT IS A FIX RATHER THAN A NARROWING,
    and the distinction is worth the paragraph.  [valid_argv]'s length
    and byte-range clauses exclude launches a kernel really performs,
    and pay priority three for priority one.  This one excludes a
    declaration that describes NO DEVICE: /dev/urandom does not run out.
    [urandom_read_iter] is [get_random_bytes_user] over the imported
    iterator, and that loops until the iterator is drained — stopping
    early only where [copy_to_iter] copies short, or where a signal is
    pending at a page boundary — and the pool is never empty once
    initialised (drivers/char/random.c, Linux v6.18.46; both functions
    were read in the 6.12.1 tree on this box, where both are the same).
    So a read of n bytes from it delivers n,
    always.  A finite [State.in_urandom] is not a device that behaved
    unusually; it is a device that does not exist.

    WHAT IT BUYS.  [Sys.Fs.ReadWrite.read_urandom] takes
    [State.rw_count_clamp count] bytes off the declared stream and
    DECLINES if fewer come back, because a short read from this device
    is not something the model has a term for.  That decline is
    reachable from a whole-program theorem — a program that opens the
    device and reads a fixed-size buffer meets it as soon as the
    declaration is shorter than the buffer — and a decline an example
    reaches makes its [Equivalence.strong_universal_T] FALSE rather
    than narrower.  With this clause the arm's [unmodeled] row is
    unreachable under [valid_input], and it is KEPT rather than deleted
    because the arm is total over [State.InputStream] and a caller
    outside [valid_input] can still meet it.  The row is the record of
    exactly what this clause excludes.

    IT IS THE ONLY CLAUSE ON AN ENVIRONMENT STREAM, and the two that
    have none stay that way.  [State.in_stdin] and [State.in_net] end,
    really and often — a pipe closes, a peer sends FIN — and a program
    has to survive it, so a clause there would exclude the case the
    model exists to check.  The difference is not that this stream is
    more important; it is that ending is a REAL BEHAVIOUR of those two
    and not of this one.

    IT SAYS NOTHING ABOUT THE CONTENTS.  Not uniform, not
    unpredictable, not fresh — only that a read yields as many bytes as
    it asked for.  The bytes themselves are an arbitrary but
    fixed stream, a parameter of the execution
    like argv and the environment. *)
Definition valid_urandom (inp : ProcInput) : Prop :=
  State.stream_infinite (in_urandom inp).

(** THE RANDOM-STREAM CLAUSE IS NOT DECIDED BY COMPUTATION, and it
    cannot be: [State.stream_infinite] is coinductive, so no [vm_compute]
    settles it and a fixture discharges it by naming the witness its
    declaration is.  Every fixture in this tree declares
    [State.default_urandom], so one tactic serves them all; a fixture
    that declares its own stream proves its own [State.stream_infinite]
    and does not reach for this. *)
Ltac valid_urandom_default :=
  try unfold valid_urandom; exact State.default_urandom_infinite.

(** Validity predicate for a [State.ProcInput].  Three fields carry no
    clause, each because every value of its type is one a process could
    really be handed: the standard-input stream's elements are [byte],
    so every colist of bytes is a stream, and a pipe that ENDS is a real
    pipe a program has to survive; every [State.NetQueue] is a
    network some environment could present; and [in_groups] is bounded
    where it is READ rather than here —
    [Kernel.Groups.getgroups_spec] declines a list longer than
    [Uapi.NGROUPS_MAX] and never reads an element, so a clause here
    would restrict the theorem without changing what it says.
    [in_nofile] is the field that looks like the third of those and is
    not: it is bounded HERE, by [valid_nofile], because the spec that
    reads it answers from it instead of declining on it.

    [in_urandom] LOOKS LIKE A FOURTH, and is not: see
    [valid_urandom] for why ending is a real behaviour of a pipe and
    not of the random device.

    [in_sigmask] is the one field constrained for the OPPOSITE reason:
    it is read back verbatim rather than bounded at its reader, so the
    clause is the only thing standing between the model and a mask no
    launch can produce.  See [valid_sigmask].

    WHY [Fs.fs_keys_relative] IS ON THE IMAGE AND NOT ON [Fs.valid_fs].
    The clause says the launch handed the process an image whose keys
    are CWD-RELATIVE: no key begins with "/".  It is a premise about the
    environment in the sense [valid_sigmask] is — no real launch
    contradicts it, because the file system a run starts from is the
    working directory it was started in, and a key there is a name
    relative to that directory — and the model cannot check it, because
    nothing in an [Fs.Fs] says where the image came from.

    It reads [State.in_image_fs], the PRE-SEED image, rather than
    [State.in_fs], and that is forced rather than stylistic.  [in_fs] is
    [State.fs_seed_tmp] of the image with the declared /tmp
    ([State.in_tmp]), and the seeding inserts each declared entry under
    the ABSOLUTE key "/tmp/<name>" — so the same clause on [in_fs] would
    be false for every input with a non-empty declaration and would
    silently delete those inputs from every theorem quantified here.
    Putting it on the image leaves [State.fs_seed_tmp_valid] and
    [FinInput.valid_input_tmp_arbitrary] intact: no /tmp
    table a launch could present is excluded.

    WHAT IT BUYS.  [Fs.valid_fs] admits the key "/dev/null", and the
    three device arms of [Sys.Fs.Open] — and [Sys.Fs.Stat]'s lookup of
    an absolute pathname — answer [unmodeled] when the map holds such a
    key or a key under it.  Without this clause, a program that always
    opens /dev/null would have ONE pathological image, admitted by every
    statement's quantifier, on which every error-free claim about it is
    false, for a reason no process can meet.  With this clause those guards are
    unreachable: [device_paths_never_seeded] below proves no key of a
    seeded image is, or lives under, any of the three device paths, and
    the guards stay in the arms as the courtesy their comments say they
    are. *)

(** THE IMAGE DESCRIBES A FILE SYSTEM: [Fs.fs_image_real] on
    [State.in_image_fs], beside the clause above and on the same
    pre-seed image, for the same seeding reason.  It says every key is
    canonical (no empty, "." or ".." component, no "//" and no trailing
    "/") and no key is also a directory another key lives in.  Ported
    from main LPS (theorem-labs/linux-process-semantics) #1776, commit
    9f9a96b29a; [Fs.fs_image_real] carries the argument.

    WHAT IT BUYS.  Without it [valid_input] admits an image with the
    keys "a" and "a/b".  No Linux file system holds that -- one name in
    one directory is one inode -- and on it the model answers as if "a"
    were a regular file and a directory at once, so a statement
    quantified here covers a launch no kernel can produce.
    [Checks.Cases.Fs.Open.fs_prefix_key_image_is_not_real] is that
    image, refused; [valid_input_image_real] below is the projection a
    proof uses. *)
Definition valid_input (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true.

(** The SAME predicate with the abort-path declaration turned on, and it
    is a separate definition rather than a parameter for the reason the
    two shapes of every other statement in this tree are separate: what a
    proof was made under has to be readable in the statement.

    THE TWO PREDICATES ARE EXHAUSTIVE and mutually exclusive on the
    field: [in_abort_terminal] is a bool, so a statement that quantifies
    over [valid_input] speaks about runs in which [tkill] (130) and
    [tgkill] (131) are declined exactly as they were before either had an
    arm, a statement that quantifies over [valid_input_abort] speaks
    about runs in which a SIGABRT the process sends itself ends it, and
    a statement that pins neither -- quantifying over
    [valid_input_either] -- asserts both.  There is no third stance and
    no way to leave the question open by accident, which is the whole
    point of the field being in the input rather than in a configuration
    a checker might forget to ascribe.

    WHY [valid_input] IS THE ONE THAT PINS [false].  Every statement in
    this tree written before the abort path had an arm quantifies over
    [valid_input], and pinning the field there is what keeps those
    statements saying what they said: with the declaration off, no
    reachable model has [State.m_abort_terminal] set, so
    [Kernel.Signal.tkill_spec] declines every call and no
    [State.KillEv] CARRYING SIGABRT can appear in any trace
    ([sstep_off_no_kill]).

    THE SIGPIPE DECLARATION IS PINNED HERE TOO, and the two are
    independent stances rather than one.  [State.in_sigpipe_default] is
    [true] under this predicate: the launch left signal 13 at SIG_DFL,
    so a write whose far end has no reader ENDS THE PROCESS and a run
    under [valid_input] can carry [KillEv 13] -- see
    [Sys.Fs.ReadWrite.write_spec] and [Sys.Fs.ReadWrite.raise_sigpipe].
    It is pinned rather than left open because that is the world every
    statement in this tree was written under, and because the other
    world is not a different number but a different OUTCOME: with
    SIG_IGN the same write returns -EPIPE and the program runs on.  A
    task that wants either other reading asks for it by name
    ([valid_input_abort], [valid_input_sigpipe_ignored]).

    THE READER DECLARATION IS PINNED HERE TOO, at [true].
    [State.in_channel_reader] says whether anything still reads
    descriptors 1 and 2, and under this predicate something does: the
    ordinary launch, whose writes to standard output are delivered.
    The reader-GONE launch -- the writing end of `prog | head -1` once
    `head` has had its line, where that same write raises signal 13 and
    ends the run -- is named rather than covered here, and a task that
    means it asks for it by name ([valid_input_channel_closed]); a task
    that means both asks for [valid_input_channel_either].  The stance
    is the stream owner's answer to dispatch://OSSV-266/ask/77724e06. *)
Definition valid_input_abort (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = true
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true.

(** Neither ABORT stance pinned: the clauses both share, and nothing
    about that declaration.  A statement quantified over this one is the
    CONJUNCTION of the two above -- it has to hold whichever stance the
    task takes -- which is what makes forgetting to choose the safe
    failure rather than the dangerous one.

    IT STILL PINS THE SIGPIPE DECLARATION, because it is the abort
    question it leaves open and only that one.  The SIGPIPE pair is
    [valid_input_sigpipe_either] below. *)
Definition valid_input_either (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true.

Lemma valid_input_either_of_valid_input : forall inp,
  valid_input inp -> valid_input_either inp.
Proof.
  (* Written so an inserted conjunct does not break it: destruct the
     hypothesis and split the goal to the same depth, both GUARDED.  A
     bare [repeat split] would also apply the constructor of
     [valid_urandom], which is coinductive. *)
  intros inp H. red in H |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma valid_input_either_of_valid_input_abort : forall inp,
  valid_input_abort inp -> valid_input_either inp.
Proof.
  (* Written so an inserted conjunct does not break it: destruct the
     hypothesis and split the goal to the same depth, both GUARDED.  A
     bare [repeat split] would also apply the constructor of
     [valid_urandom], which is coinductive. *)
  intros inp H. red in H |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(** The exhaustiveness the paragraph above claims, as a lemma rather
    than as a sentence: an input the shared clauses accept satisfies one
    of the two pinned predicates, because a bool has two values. *)
Lemma valid_input_either_splits : forall inp,
  valid_input_either inp -> valid_input inp \/ valid_input_abort inp.
Proof.
  intros inp (a & b & c & k & r & d & e & f & g & s & n & v & u & L).
  destruct (in_abort_terminal inp) eqn:Hab.
  - right.
    try red;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
  - left.
    try red;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(** * The SIGPIPE declaration: the same predicate with signal 13 ignored

    THE OTHER WORLD A LAUNCH CAN PUT THIS PROGRAM IN, written the way
    the abort stance above is, and for the same reason: what a proof was
    made under has to be readable in the statement.  Here the launcher
    ran `signal(SIGPIPE, SIG_IGN)` before execve and the disposition
    survived it, so [Sys.Fs.ReadWrite.raise_sigpipe] discards the signal
    and a write to a far end with no reader is -EPIPE with the process
    STILL RUNNING.  Every other clause is [valid_input]'s, the abort
    declaration included.

    WHAT A STATEMENT QUANTIFIED OVER THIS ONE IS WORTH.  It is the
    reading a program that handles -EPIPE itself was written for -- a
    daemon, a filter under a service manager -- and under it no write
    arm can end the run, so a halts statement is not refuted by a
    reader-less channel.  It is NOT the safer predicate: it asserts
    something about the launch that the ordinary one does not, and a
    proof made under it says nothing about the ordinary launch. *)
Definition valid_input_sigpipe_ignored (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = false
  /\ in_channel_reader inp = true.

(** Neither SIGPIPE stance pinned: the clauses both share, and nothing
    about the disposition.  A statement quantified over this one is the
    CONJUNCTION of [valid_input] and [valid_input_sigpipe_ignored], so a
    task that forgets to say which launch it means is held to both --
    the same safe failure [valid_input_either] gives for the abort
    stance. *)
Definition valid_input_sigpipe_either (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_channel_reader inp = true.

Lemma valid_input_sigpipe_either_of_valid_input : forall inp,
  valid_input inp -> valid_input_sigpipe_either inp.
Proof.
  intros inp H. red in H |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma valid_input_sigpipe_either_of_valid_input_sigpipe_ignored : forall inp,
  valid_input_sigpipe_ignored inp -> valid_input_sigpipe_either inp.
Proof.
  intros inp H. red in H |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(** The exhaustiveness above as a lemma rather than as a sentence, the
    twin of [valid_input_either_splits]: a bool has two values. *)
Lemma valid_input_sigpipe_either_splits : forall inp,
  valid_input_sigpipe_either inp ->
  valid_input inp \/ valid_input_sigpipe_ignored inp.
Proof.
  (* The hypotheses are taken apart and the goal is rebuilt BY SPLITTING,
     not by naming a position.  An explicit [conj] chain hard-codes the
     order of the conjunction it builds, so moving a conjunct silently
     puts a proof of one fact where another is expected — which is what
     this very lemma did when the two signal-death pins moved to the end,
     and it is the proof-side twin of the consumer peels this reorder
     exists to protect.  [repeat split] does not care about the order,
     and [assumption] cannot pick a wrong one: the two pins differ in
     their bool, so only the branch's own [Hsp] matches. *)
  intros inp (a & b & c & k & r & d & e & f & g & h & n & v & u & L).
  destruct (in_sigpipe_default inp) eqn:Hsp.
  - left.  unfold valid_input.
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
  - right. unfold valid_input_sigpipe_ignored.
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(** * THE READER DECLARATION: PINNED PRESENT, AND THE OTHER WORLD NAMED

    [State.in_channel_reader] says whether anything still reads
    descriptors 1 and 2.  [valid_input] above PINS IT TO [true]: the
    ordinary launch is the one whose standard output is read, and a
    statement quantified over [valid_input] speaks about that launch
    and no other.  That is the stance the stream owner chose for
    dispatch://OSSV-266/ask/77724e06 -- pin the reader, and name the
    reader-gone launch so a proof can ask for it -- and it is the shape
    the abort declaration already has: [valid_input] pins
    [State.in_abort_terminal] to [false] and [valid_input_abort] names
    the other world.

    WHY THE PIN RATHER THAN BOTH READINGS.  With the field unpinned
    every ordinary statement would also be a claim about a run whose
    first write to standard output KILLS IT (signal 13 at SIG_DFL,
    which [valid_input] pins as well), so a halts statement or a
    trace statement would silently have to cover a death the task
    never meant to describe.  The pin says which launch the tree is
    about; the predicates below say the other one.

    [valid_input_channel_closed] is the reader-GONE launch named, in
    the shape [valid_input_abort] has for the abort declaration: every
    clause of [valid_input] with the reader pinned to [false].  It is
    NOT the safer predicate -- it asserts something about the launch
    that [valid_input] does not, and a proof made under it says nothing
    about a run whose output is read.  What it buys is a world where
    [Sys.Fs.ReadWrite.write_spec]'s channel arm takes the reader-less
    branch, which is what [Common.CatSimSigpipe] proves a whole run of.

    [valid_input_channel_either] pins neither value, the twin of
    [valid_input_either]: a statement quantified over it is the
    CONJUNCTION of the two readings, which is what makes forgetting to
    choose the safe failure rather than the dangerous one. *)
Definition valid_input_channel_closed (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = false.

(** Neither reader stance pinned: the clauses both share, and nothing
    about that declaration. *)
Definition valid_input_channel_either (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true.

Lemma valid_input_channel_either_of_valid_input : forall inp,
  valid_input inp -> valid_input_channel_either inp.
Proof.
  (* Written so an inserted conjunct does not break it: destruct the
     hypothesis and split the goal to the same depth, both GUARDED.  A
     bare [repeat split] would also apply the constructor of
     [valid_urandom], which is coinductive. *)
  intros inp H. red in H |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma valid_input_channel_either_of_valid_input_channel_closed : forall inp,
  valid_input_channel_closed inp -> valid_input_channel_either inp.
Proof.
  intros inp H. red in H |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(** The exhaustiveness the paragraph above claims, as a lemma rather
    than as a sentence, the twin of [valid_input_either_splits]: a bool
    has two values, so an input the shared clauses accept is one of the
    two named launches. *)
Lemma valid_input_channel_either_splits : forall inp,
  valid_input_channel_either inp ->
  valid_input inp \/ valid_input_channel_closed inp.
Proof.
  intros inp H.
  destruct (in_channel_reader inp) eqn:Hcr; [left | right];
    red in H |- *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(** THE READER CLAUSE under each named reading, as an accessor rather
    than as a position, for the reason [valid_input_abort_terminal]
    below is one. *)
Lemma valid_input_channel_reader : forall inp,
  valid_input inp -> in_channel_reader inp = true.
Proof.
  intros inp H. red in H.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma valid_input_channel_closed_reader : forall inp,
  valid_input_channel_closed inp -> in_channel_reader inp = false.
Proof.
  intros inp H. red in H.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

(** THE SIGPIPE DECLARATION, as an accessor rather than as a position,
    for the reason [valid_input_abort_terminal] below is one: this
    predicate grows a conjunct whenever the input class learns to say
    something new, and a caller that reached in by position would then
    name a DIFFERENT clause rather than fail. *)
Lemma valid_input_sigpipe_default : forall inp,
  valid_input inp -> in_sigpipe_default inp = true.
Proof.
  intros inp Hv. red in Hv.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

(** The same clause under the ignoring stance, where it is [false]. *)
Lemma valid_input_sigpipe_ignored_sigpipe_default : forall inp,
  valid_input_sigpipe_ignored inp -> in_sigpipe_default inp = false.
Proof.
  intros inp Hv. red in Hv.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

(** * The address-space declaration: the same predicate per size

    Separate definitions rather than a parameter, for the reason the
    abort stances above are: what a proof was made under has to be
    readable in the statement.  Every statement in this tree was written
    against the Sv48 kernel, and [valid_input] (and both abort stances)
    pin the size there, which keeps those statements saying what they
    said; a task that runs on another kernel asks for it by name, and
    what it gets today is spelled out at [Equivalence.strong_equiv_va]
    and at [State.VaSize].  The two other sizes are stated with the
    abort declaration OFF, the default stance; a task wanting both the
    abort path and another size has no predicate here yet, and the day
    one is needed it is written the way these are.

    [valid_input_va_any] pins the abort stance off and nothing about
    the size: a statement quantified over it holds under every size, so
    a task that says nothing about its kernel is held to all three
    readings rather than to the default. *)
Definition valid_input_sv39 (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv39
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true.

Definition valid_input_sv57 (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv57
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true.

Definition valid_input_va_any (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true.

Lemma valid_input_image_real : forall inp,
  valid_input inp -> fs_image_real (in_image_fs inp) = true.
Proof.
  intros inp Hv. unfold valid_input in Hv.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma valid_input_va_size : forall inp, valid_input inp -> in_va_size inp = Sv48.
Proof.
  intros inp Hv. unfold valid_input in Hv.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

(** THE ABORT DECLARATION, as an accessor rather than as a position.
    [valid_input] pins [State.in_abort_terminal] to [false] — that is
    what makes [Kernel.Signal.tkill_spec] decline every call under it,
    and therefore what makes a [State.KillEv] CARRYING SIGABRT
    unreachable for every statement quantified over this predicate
    ([sstep_off_no_kill]).  A SIGPIPE kill is a separate declaration,
    [valid_input_sigpipe_default] above, which this predicate pins the
    other way round: under [valid_input] signal 13 IS at SIG_DFL and a
    reader-less write ends the run; see [Sys.Fs.ReadWrite.write_spec].
    Consumers want that one clause and nothing else.

    NAMED, BECAUSE THE POSITION MOVES.  This predicate grows a conjunct
    whenever the input class learns to say something new, and a caller
    that reached in by position ([intros inp (_ & … & H & _)]) then
    names a DIFFERENT clause rather than failing — it goes on compiling
    and quietly stops being about the declaration.  Callers should take
    this lemma instead, so that an insertion is one re-proof here and
    none anywhere else.

    The proof is itself position-independent: it splits every
    conjunction and lets [assumption] find the clause of the right
    shape, so an insertion does not re-break it either.  [valid_input_va_size]
    above and [valid_input_abort_va_size] below read the same way,
    for the same reason. *)
Lemma valid_input_abort_terminal : forall inp,
  valid_input inp -> in_abort_terminal inp = false.
Proof.
  intros inp Hv. unfold valid_input in Hv.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

(** THE RANDOM-STREAM CLAUSE, as an accessor rather than as a position,
    and for the reason above: it is the LAST conjunct today, so a caller
    that reached in by position would be the first thing the next
    insertion breaks.  It is also the clause with no computational
    content — [State.stream_infinite] is coinductive — so a consumer
    that wants it wants it by name.

    [Checks.Examples.the_random_clause_is_what_the_fixture_carries]
    fires it in both directions: the fixtures satisfy it, and the empty
    declaration does not. *)
Lemma valid_input_urandom : forall inp, valid_input inp -> valid_urandom inp.
Proof.
  intros inp Hv. unfold valid_input in Hv.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

(** The same clause under the declared stance, where it is [true]. *)
Lemma valid_input_abort_abort_terminal : forall inp,
  valid_input_abort inp -> in_abort_terminal inp = true.
Proof.
  intros inp Hv. unfold valid_input_abort in Hv.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

(** Both abort stances pin the same size. *)
Lemma valid_input_abort_va_size : forall inp,
  valid_input_abort inp -> in_va_size inp = Sv48.
Proof.
  intros inp Hv. unfold valid_input_abort in Hv.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma valid_input_va_any_of_valid_input : forall inp,
  valid_input inp -> valid_input_va_any inp.
Proof.
  (* Written so an inserted conjunct does not break it: destruct the
     hypothesis and split the goal to the same depth, both GUARDED.  A
     bare [repeat split] would also apply the constructor of
     [valid_urandom], which is coinductive. *)
  intros inp H. red in H |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma valid_input_va_any_of_valid_input_sv39 : forall inp,
  valid_input_sv39 inp -> valid_input_va_any inp.
Proof.
  (* Written so an inserted conjunct does not break it: destruct the
     hypothesis and split the goal to the same depth, both GUARDED.  A
     bare [repeat split] would also apply the constructor of
     [valid_urandom], which is coinductive. *)
  intros inp H. red in H |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma valid_input_va_any_of_valid_input_sv57 : forall inp,
  valid_input_sv57 inp -> valid_input_va_any inp.
Proof.
  (* Written so an inserted conjunct does not break it: destruct the
     hypothesis and split the goal to the same depth, both GUARDED.  A
     bare [repeat split] would also apply the constructor of
     [valid_urandom], which is coinductive. *)
  intros inp H. red in H |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(** Exhaustiveness as a lemma: an input the shared clauses accept
    satisfies exactly one of the three pinned predicates, because the
    declaration has three values. *)
Lemma valid_input_va_any_splits : forall inp,
  valid_input_va_any inp ->
  valid_input inp \/ valid_input_sv39 inp \/ valid_input_sv57 inp.
Proof.
  intros inp (a & b & c & k & r & d & e & f & g & h & s & n & u & L).
  destruct (in_va_size inp) eqn:Hv.
  - right; left.
    try red;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
  - left.
    try red;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
  - right; right.
    try red;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(** * The hardware-capability declaration: the same predicate per word

    [valid_hwcap] admits two words and THE DEFAULT STAYS THAT
    DISJUNCTION.  The reason is the one its own comment gives:
    [RiscvSemantics.decode_exec_accesses] answers a word it cannot
    decode with [MachineUnmodeled] rather than a trap, so the model does
    not claim the hart lacks V and must not publish a word that says so.
    Nothing below weakens that.  What the two predicates add is the
    TASK's declaration -- "the kernel this task runs under publishes
    THIS word" -- in the shape [valid_input_sv39] gives the
    address-space declaration, and for the same reason: what a proof was
    made under has to be readable in the statement.

    NAMED PREDICATES RATHER THAN A PARAMETER.  A predicate parameterised
    by the word could be instantiated at a word [valid_hwcap] refuses --
    the zero the absent entry effectively delivered, an A-less mask, a
    mask with a letter [riscv_fill_hwcap] never assigns -- and the
    resulting statement would hold VACUOUSLY, since no launch produces
    such an input.  Two definitions cannot be instantiated at all, and
    [valid_input_hwcap_splits] says the pair is exactly the default.

    WHY A TASK WOULD DECLARE.  Under the permissive default a statement
    ranges over both words, so a runtime that dispatches on the V bit
    must be equivalent under [hwcap_rv64gcv] too, and the first vector
    instruction it executes is a word [DecodeC.decode_any] returns
    [None] for: the run is [MachineUnmodeled] and the statement is FALSE
    as issued.  That answer does not change here.  What changes is that
    a task can say which hart it runs on.  The case that motivates
    it is the PROBE: a binary that reads [vlenb] -- a V-extension CSR --
    only to learn whether a vector unit is there.  That read DECODES,
    unlike the vector instruction; what declines it is [Sem.csr_slice],
    which resolves only the fcsr aliases, so [Sem.exec_csr] answers
    [Sem.EIllegal] and the run is [MachineUnmodeled] all the same
    ([Checks.Cases.Hwcap] pins each level and the composition).  Under the permissive
    default every statement about such a binary is false; under
    [valid_input_hwcap_rv64gc] the advertised word has no V bit, the
    probe is never taken, and the statement is the one the task can
    prove.  The declaration is the TASK's claim about its environment,
    not the model's claim about the silicon, which is why it is a field
    of the input and a predicate over that field rather than anything
    the spec arms read.

    BOTH KEEP THE ABORT DECLARATION OFF AND THE SIZE AT [Sv48], exactly
    as [valid_input_sv39] does.  The abort stance has its own pair below
    ([valid_input_abort_hwcap_rv64gc] and its twin), because a task asked
    for that cell.  A task wanting a declared word together with another
    address-space size, or with the stance left open, has no predicate
    here yet, and the day one is needed it is written the way these
    are. *)
Definition valid_input_hwcap_rv64gc (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ in_hwcap inp = hwcap_rv64gc
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true.

Definition valid_input_hwcap_rv64gcv (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ in_hwcap inp = hwcap_rv64gcv
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true.

(** Each declaration is a NARROWING of the default, so a statement
    quantified over [valid_input] is about every input either predicate
    accepts.  That direction is what makes the declaration a restriction
    on the task rather than a widening of the theorem. *)
Lemma valid_input_of_valid_input_hwcap_rv64gc : forall inp,
  valid_input_hwcap_rv64gc inp -> valid_input inp.
Proof.
  intros inp (a & b & c & k & r & d & e & f & g & h & v & n & u & L).
  try red;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma valid_input_of_valid_input_hwcap_rv64gcv : forall inp,
  valid_input_hwcap_rv64gcv inp -> valid_input inp.
Proof.
  intros inp (a & b & c & k & r & d & e & f & g & h & v & n & u & L).
  try red;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(** …and the two are EXHAUSTIVE on the default, because [valid_hwcap] is
    a two-word disjunction and nothing else in [valid_input] mentions
    the field.  This is the lemma that makes the default "the two"
    rather than "at least the two": there is no third word a statement
    quantified over [valid_input] would be held to and neither
    declaration covers. *)
Lemma valid_input_hwcap_splits : forall inp,
  valid_input inp ->
  valid_input_hwcap_rv64gc inp \/ valid_input_hwcap_rv64gcv inp.
Proof.
  intros inp (a & b & c & k & r & d & e & f & [g | g] & h & s & n & v & u).
  - left.
    try red;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
  - right.
    try red;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(** The declared word, read back out of the predicate.  A statement's
    consumer needs this to know WHICH word the auxv publishes under the
    declaration ([StackLayout.auxv_entries] carries [in_hwcap] verbatim),
    and it is what [Checks.Cases.Hwcap] fires to say so. *)
Lemma valid_input_hwcap_rv64gc_word : forall inp,
  valid_input_hwcap_rv64gc inp -> in_hwcap inp = hwcap_rv64gc.
Proof.
  intros inp Hv. unfold valid_input_hwcap_rv64gc in Hv.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma valid_input_hwcap_rv64gcv_word : forall inp,
  valid_input_hwcap_rv64gcv inp -> in_hwcap inp = hwcap_rv64gcv.
Proof.
  intros inp Hv. unfold valid_input_hwcap_rv64gcv in Hv.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

(** ** The same declaration under the ABORT stance

    The two predicates above pin the abort declaration OFF, because that
    is the stance [valid_input] pins and the one every statement written
    before the abort path had an arm quantifies over.  A task whose
    binary probes for a vector unit AND wants the abort path modeled
    needs the other cell, so it is written here rather than left for the
    day it is asked for: the conjuncts of [valid_input_abort] verbatim,
    with [valid_hwcap (in_hwcap inp)] replaced by the equation.

    WHICH CELLS EXIST AFTER THIS.  The declaration crosses with the
    abort stance and with nothing else.  [valid_input_either] gets no
    hwcap predicate -- a statement that declines to choose a stance is
    the conjunction of the two that do, so a task wanting both a
    declared word and no stance proves the two declared statements --
    and neither do [valid_input_sv39], [valid_input_sv57] or
    [valid_input_va_any], because no task runs on another kernel and
    probes for V.  A task wanting one of those combinations has no
    predicate here yet, and the day one is needed it is written the way
    these are. *)
Definition valid_input_abort_hwcap_rv64gc (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ in_hwcap inp = hwcap_rv64gc
  /\ in_abort_terminal inp = true
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true.

Definition valid_input_abort_hwcap_rv64gcv (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ in_hwcap inp = hwcap_rv64gcv
  /\ in_abort_terminal inp = true
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true.

Lemma valid_input_abort_of_valid_input_abort_hwcap_rv64gc : forall inp,
  valid_input_abort_hwcap_rv64gc inp -> valid_input_abort inp.
Proof.
  intros inp (a & b & c & k & r & d & e & f & g & h & v & n & u & L).
  try red;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma valid_input_abort_of_valid_input_abort_hwcap_rv64gcv : forall inp,
  valid_input_abort_hwcap_rv64gcv inp -> valid_input_abort inp.
Proof.
  intros inp (a & b & c & k & r & d & e & f & g & h & v & n & u & L).
  try red;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma valid_input_abort_hwcap_splits : forall inp,
  valid_input_abort inp ->
  valid_input_abort_hwcap_rv64gc inp \/ valid_input_abort_hwcap_rv64gcv inp.
Proof.
  intros inp (a & b & c & k & r & d & e & f & [g | g] & h & s & n & v & u).
  - left.
    try red;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
  - right.
    try red;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma valid_input_abort_hwcap_rv64gc_word : forall inp,
  valid_input_abort_hwcap_rv64gc inp -> in_hwcap inp = hwcap_rv64gc.
Proof.
  intros inp Hv. unfold valid_input_abort_hwcap_rv64gc in Hv.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma valid_input_abort_hwcap_rv64gcv_word : forall inp,
  valid_input_abort_hwcap_rv64gcv inp -> in_hwcap inp = hwcap_rv64gcv.
Proof.
  intros inp Hv. unfold valid_input_abort_hwcap_rv64gcv in Hv.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

(* =========================================================================
   The image premise, consumed: the device arms' guards are unreachable

   [valid_input]'s [Fs.fs_keys_relative] conjunct is a premise about the
   environment, and a premise earns its place by being USED.  What it is
   for is here: the three device arms of [Sys.Fs.Open] and the key
   lookup of [Sys.Fs.Stat.newfstatat_core_spec] each ask the initial
   file system whether it holds an absolute path, or something under it,
   and answer [unmodeled] when it does.  Under the premise it never
   does, so those branches are dead on every valid input and the guards
   stay in the arms as the courtesy their comments say they are — NO ARM
   IS CHANGED by this: the premise makes the guards dead, it does not
   delete them.

   The lemmas live here rather than in [State] because they name
   [Sys.Fs.Namei.fs_under] and the arms' own path constants, which sit
   above [State.v]; the seeding half of the argument
   ([State.seeded_absolute_key_is_tmp]) is down there where the seeding
   is.
   ========================================================================= *)

(** THE ONE FACT THE ARMS NEED.  [p] begins with the separator and
    DIVERGES from the seeding prefix at a byte position both of them
    have.  Then no key of a seeded image is [p], and none lives under
    it — so [Fs.fs_lookup] misses and [Sys.Fs.Namei.fs_under] is false.

    Both halves come from [State.seeded_absolute_key_is_tmp]: a key is
    relative, and then it does not even start the way [p] does, or the
    seeding minted it and it is [State.tmp_key n], which agrees with
    [State.tmp_prefix] at position [i] where [p] does not.  The
    divergence is stated as an index rather than as "p is not under
    /tmp" because the [fs_under] half needs more than non-prefixhood:
    "/tmp" is not a /tmp key and yet every /tmp key lives under it. *)
Lemma absolute_divergent_not_seeded : forall fs t r i a b,
  fs_keys_relative fs ->
  nth_error (path_slash_byte :: r) i = Some a ->
  nth_error tmp_prefix i = Some b ->
  a <> b ->
  fs_lookup (fs_seed_tmp fs t) (path_slash_byte :: r) = None
  /\ fs_under (fs_seed_tmp fs t) (path_slash_byte :: r) = false.
Proof.
  intros fs t r i a b Hrel Hp Ht Hab.
  assert (Hi : (i < length (path_slash_byte :: r))%nat)
    by (apply nth_error_Some; rewrite Hp; discriminate).
  assert (Hj : (i < length tmp_prefix)%nat)
    by (apply nth_error_Some; rewrite Ht; discriminate).
  pose proof (State.seeded_absolute_key_is_tmp t fs Hrel) as Hall.
  split.
  - apply fs_lookup_none_of_keys.
    eapply Forall_impl; [|exact Hall]. intros [q d] Hq. cbn [fst] in Hq |- *.
    destruct Hq as [Hq|[n Hq]]; intros Heq.
    + rewrite Heq in Hq. unfold key_is_relative in Hq. exact (Hq eq_refl).
    + assert (Hx : nth_error q i = Some b)
        by (rewrite Hq; unfold tmp_key; rewrite nth_error_app1 by exact Hj; exact Ht).
      rewrite Heq, Hp in Hx. inversion Hx. now apply Hab.
  - apply fs_under_false_of_keys.
    eapply Forall_impl; [|exact Hall]. intros [q d] Hq. cbn [fst] in Hq |- *.
    destruct Hq as [Hq|[n Hq]].
    + destruct q as [|c q]; [reflexivity|].
      unfold key_is_relative in Hq. cbn [dir_prefixb].
      destruct (bv_eqb path_slash_byte c) eqn:Hc; [|reflexivity].
      exfalso. apply bv_eqb_eq in Hc. apply Hq. now symmetry.
    + destruct (dir_prefixb (path_slash_byte :: r) q) eqn:Hd; [|reflexivity].
      exfalso. apply dir_prefixb_app in Hd. destruct Hd as [rest Hrest].
      assert (Hx : nth_error q i = Some b)
        by (rewrite Hq; unfold tmp_key; rewrite nth_error_app1 by exact Hj; exact Ht).
      rewrite Hrest in Hx. rewrite nth_error_app1 in Hx by exact Hi.
      rewrite Hp in Hx. inversion Hx. now apply Hab.
Qed.

(** The three DEVICE paths of [Sys.Fs.Open], each of which diverges from
    "/tmp/" at its second byte ('d', 'e', 'd' against 't').  This is the
    statement the arms' image guards are unreachable: each reads
    [fs_lookup (m_fs m) p] and, on [None], [fs_under (m_fs m) p], so
    both branches that answer [unmodeled] there are ruled out.  The
    paths are the arms' OWN constants, so a path that moves moves here
    too. *)
Lemma device_paths_never_seeded : forall fs t p,
  fs_keys_relative fs ->
  In p [devnull_path; localtime_path; urandom_path] ->
  fs_lookup (fs_seed_tmp fs t) p = None
  /\ fs_under (fs_seed_tmp fs t) p = false.
Proof.
  intros fs t p Hrel Hin.
  (* 'd' and 'e' against the 't' of "/tmp/": the second byte is where
     each of the three parts company with the seeding prefix. *)
  assert (Hd : Z_to_bv 8 100 <> Z_to_bv 8 116)
    by (intros H; apply (proj2 (bv_eqb_eq _ _)) in H; vm_compute in H; discriminate).
  assert (He : Z_to_bv 8 101 <> Z_to_bv 8 116)
    by (intros H; apply (proj2 (bv_eqb_eq _ _)) in H; vm_compute in H; discriminate).
  destruct Hin as [H|[H|[H|[]]]]; subst p.
  - apply (absolute_divergent_not_seeded fs t _ 1%nat (Z_to_bv 8 100) (Z_to_bv 8 116) Hrel);
      [reflexivity | reflexivity | exact Hd].
  - apply (absolute_divergent_not_seeded fs t _ 1%nat (Z_to_bv 8 101) (Z_to_bv 8 116) Hrel);
      [reflexivity | reflexivity | exact He].
  - apply (absolute_divergent_not_seeded fs t _ 1%nat (Z_to_bv 8 100) (Z_to_bv 8 116) Hrel);
      [reflexivity | reflexivity | exact Hd].
Qed.

(** The same, at a model whose file system is the run's initial one.

    [m] is any model carrying [State.in_fs inp] — the initial model
    [State.init_model] builds is one, and so is every later state that
    has not written the map.  Whether a LATER state can be one is a
    question about the write arms rather than about the premise: the
    only specs that mint a key are [Sys.Fs.Open]'s create arms, which
    sit behind the separator gate, and the /tmp arm, whose key is
    [State.tmp_key] of one component — so no run-time creation puts a
    device path in the map.  That is an argument about arms this lemma
    does not quantify over, so it is said here and not claimed by the
    statement. *)
Lemma valid_input_device_guards_unreachable : forall inp m p,
  fs_keys_relative (in_image_fs inp) ->
  m_fs m = in_fs inp ->
  In p [devnull_path; localtime_path; urandom_path] ->
  fs_lookup (m_fs m) p = None /\ fs_under (m_fs m) p = false.
Proof.
  intros inp m p Hrel Hm Hin. rewrite Hm. unfold in_fs.
  now apply device_paths_never_seeded.
Qed.

(** [Sys.Fs.Stat.newfstatat_core_spec]'s half of the same fact.  That
    spec answers [unmodeled] when the path it was handed IS a key, and
    -ENOENT when it is not; under the premise every absolute pathname
    that is not a /tmp key misses, so the [unmodeled] branch is
    unreachable for it and the answer is the real -ENOENT.  Stated over
    the divergence index rather than over a list of paths, because
    [newfstatat] takes its path from the program rather than from a
    constant. *)
Lemma valid_input_absolute_key_absent : forall inp m r i a b,
  fs_keys_relative (in_image_fs inp) ->
  m_fs m = in_fs inp ->
  nth_error (path_slash_byte :: r) i = Some a ->
  nth_error tmp_prefix i = Some b ->
  a <> b ->
  fs_lookup (m_fs m) (path_slash_byte :: r) = None
  /\ fs_under (m_fs m) (path_slash_byte :: r) = false.
Proof.
  intros inp m r i a b Hrel Hm Hp Ht Hab. rewrite Hm. unfold in_fs.
  exact (absolute_divergent_not_seeded _ _ r i a b Hrel Hp Ht Hab).
Qed.

Lemma refuse_reason_budget_implies_refused : forall i m,
  alloc_refuse_reason i m = Some RefuseBudget -> alloc_budget_refused_b i m = true.
Proof.
  intros i m H. unfold alloc_refuse_reason in H.
  destruct (alloc_budget_refused_b i m) eqn:E.
  - reflexivity.
  - discriminate H.
Qed.

(** [budget_refused_at] with the grant disjunct narrowed to
    [alloc_refuse_reason i m = Some RefuseBudget]; the two first-touch
    clauses are unchanged.  It implies [budget_refused_at], so
    [~ run_budget_only_refused] admits every input [~ run_budget_refused]
    admits, and also those whose only refusal is oversize. *)
Definition budget_only_refused_at (segs : list Segment) (c : config) : Prop :=
  m_halted (cfg_model c) = None /\
  ( (ms_svc_pending (cfg_ms c) = None /\
     exists report,
       RiscvSemantics.step_accesses segs (cfg_ms c) = MachineOk report /\
       materialize_model_accesses (cfg_model c) (@accessed_ranges _ report) = None)
  \/ (exists x8, ms_svc_pending (cfg_ms c) = Some x8 /\
       ( alloc_refuse_reason (sys_input segs (cfg_ms c) x8) (cfg_model c) = Some RefuseBudget
       \/ exists eff model' evs,
            syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) (Ok eff model' evs)
            /\ m_halted model' = None
            /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None)) ).

Lemma budget_only_refused_at_implies : forall segs c,
  budget_only_refused_at segs c -> budget_refused_at segs c.
Proof.
  intros segs c [Hh Hd]. split; [exact Hh|].
  destruct Hd as [H1 | (x8 & Hp & [Hb | H3])].
  - left; exact H1.
  - right. exists x8. split; [exact Hp|]. left.
    apply refuse_reason_budget_implies_refused; exact Hb.
  - right. exists x8. split; [exact Hp|]. right. exact H3.
Qed.

Definition reaches_budget_only_refused (segs : list Segment) (c0 : config) : Prop :=
  exists tr c, star segs c0 tr c /\ budget_only_refused_at segs c.

Lemma reaches_budget_only_refused_implies : forall segs c0,
  reaches_budget_only_refused segs c0 -> reaches_budget_refused segs c0.
Proof.
  intros segs c0 (tr & c & Hstar & Hb). exists tr, c. split; [exact Hstar|].
  apply budget_only_refused_at_implies; exact Hb.
Qed.

Definition run_budget_only_refused (img : Image) (lim : Z) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    reaches_budget_only_refused segs (init_config segs pc ph sp brk0 mbase rnd lim inp)
  end.

Lemma run_budget_only_refused_implies : forall img lim en inp,
  run_budget_only_refused img lim en inp -> run_budget_refused img lim en inp.
Proof.
  intros [segs pc ph] lim [sp brk0 mbase rnd] inp H.
  cbn in *. apply reaches_budget_only_refused_implies; exact H.
Qed.

(** The configured form, over [star_cfg], beside
    [reaches_budget_refused_cfg].  The same lifts hold: to the
    configured released mark, to the unfiltered finer mark (a
    configuration removes executions and adds none), and the two agree
    at [may_fail_cfg]. *)
Definition reaches_budget_only_refused_cfg (segs : list Segment) (cfg : SpuriousCfg)
    (c0 : config) : Prop :=
  exists tr c, star_cfg segs cfg c0 tr c /\ budget_only_refused_at segs c.

Lemma reaches_budget_only_refused_cfg_implies : forall segs cfg c0,
  reaches_budget_only_refused_cfg segs cfg c0 -> reaches_budget_refused_cfg segs cfg c0.
Proof.
  intros segs cfg c0 (tr & c & Hstar & Hb). exists tr, c. split; [exact Hstar|].
  apply budget_only_refused_at_implies; exact Hb.
Qed.

Lemma reaches_budget_only_refused_cfg_sub : forall segs cfg c0,
  reaches_budget_only_refused_cfg segs cfg c0 -> reaches_budget_only_refused segs c0.
Proof.
  intros segs cfg c0 (tr & c & Hstar & Hb).
  exists tr, c. split; [exact (star_cfg_sub segs cfg _ _ _ Hstar) | exact Hb].
Qed.

Lemma reaches_budget_only_refused_cfg_may_fail : forall segs c0,
  reaches_budget_only_refused segs c0
  <-> reaches_budget_only_refused_cfg segs may_fail_cfg c0.
Proof.
  intros segs c0. split; intros (tr & c & Hstar & Hb); exists tr, c; split; try exact Hb.
  - apply star_cfg_may_fail; exact Hstar.
  - apply star_cfg_may_fail; exact Hstar.
Qed.

(** The configured run's form, the [match] of [run_scfg]. *)
Definition run_scfg_budget_only_refused (cfg : SpuriousCfg) (img : Image) (lim : Z)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    reaches_budget_only_refused_cfg segs cfg
      (init_config segs pc ph sp brk0 mbase rnd lim inp)
  end.

Lemma run_scfg_budget_only_refused_implies : forall cfg img lim en inp,
  run_scfg_budget_only_refused cfg img lim en inp ->
  run_scfg_budget_refused cfg img lim en inp.
Proof.
  intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp H.
  exact (reaches_budget_only_refused_cfg_implies segs cfg _ H).
Qed.

Lemma run_scfg_budget_only_refused_sub : forall cfg img lim en inp,
  run_scfg_budget_only_refused cfg img lim en inp ->
  run_budget_only_refused img lim en inp.
Proof.
  intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp H.
  exact (reaches_budget_only_refused_cfg_sub segs cfg _ H).
Qed.

Lemma run_scfg_budget_only_refused_may_fail : forall img lim en inp,
  run_budget_only_refused img lim en inp
  <-> run_scfg_budget_only_refused may_fail_cfg img lim en inp.
Proof.
  intros [segs pc ph] lim [sp brk0 mbase rnd] inp.
  exact (reaches_budget_only_refused_cfg_may_fail segs _).
Qed.
