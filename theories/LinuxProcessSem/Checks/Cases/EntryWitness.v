(** * LinuxProcessSem.Checks.Cases.EntryWitness — the two directions of the start-state defect

    Acceptance A2 of dispatch://OSSV-257, in one file: a Linux start
    state the model USED NOT TO ADMIT, and a start state it USED TO
    ADMIT that no Linux launch gives.  Each half is a check that FAILS
    on the model as it stood before [Run.entry_launch_ok_va] and passes
    after it; each header below says what it would have shown.

    The fixture is the spec's, without randomization: argv ["a"], no
    envp, exec file name "a", uid = gid = 1000, AT_HWCAP without V,
    CONFIG_RSEQ on, a guard gap of 256 pages, [vm.mmap_rnd_bits] 18, no
    vector unit, no cache leaves, the first vDSO image.  With those the
    auxv has 29 entries, [items] is 4, C = 512 and L = 4, so the whole
    block is 528 bytes and the admitted stack pointers for
    [ed_top = STACK_TOP] run from 0x7fffffffedf0 to 0x7ffffffffdf0.

    (a) THE MISSING START STATE.  Linux puts argv[0] at
        [top - 8 - L] = 0x7ffffffffff4 — [create_init_stack_vma]
        (mm/vma_exec.c) skips the top eight bytes and
        [do_execveat_common] (fs/exec.c) copies the strings down from
        there — so the eight bytes at sp + 8 hold that address and
        [argv[0] - sp] is 516.  Before this change the model laid its
        own ten-entry vector and put argv[0] at sp + 192, so those
        bytes read 0x7ffffffffeb0 and [argv[0] - sp] was 192 at EVERY
        admitted entry.  [witness_argv0_pointer] is the byte check and
        [admitted_string_base_far_above_sp] is the statement about the
        whole admitted SET: the program of the spec's Problem section,
        which aborts when [argv[0] - sp] is above 0x100, aborts on
        Linux and was provably abort-free in the model.

    (b) THE EXTRA START STATE.  Two images with no system calls.
        [low_image] faults when sp is below 0x7fffbf000000 and spins
        forever otherwise; [high_image] faults when sp is above
        0x7fffffc00000 and spins forever otherwise.  Each run's trace
        set is the single empty trace, so [Classifier.agree] on this
        input turns on its error conjunct alone: one image may fault at
        some admitted entry exactly when the other may.  Before this
        change the model admitted sp = [State.sp_window_lo] =
        0x7fff80000000, where [low_image] faults, so both sides of that
        conjunct held and [agree] was provable — and false on Linux,
        whose lowest stack pointer for this input is 0x7fffffffddf0,
        far above [low_image]'s threshold, while [high_image] faults at
        every launch with randomization off.  [low_image_error_free]
        and [refutes_agree] are the two halves of the refutation.

    Every constant is Linux v6.18.46, commit 1f99e9ab748f.
    [Checks/Examples.v] re-exports this module; the helper lemmas are
    [Local], so the re-export adds only the fixture, the images and the
    results. *)

From Stdlib Require Import ZArith NArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence Classifier.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The fixture
   ========================================================================= *)

(** The launch facts: no randomization ([kernel.randomize_va_space] 0,
    or an [ADDR_NO_RANDOMIZE] personality; fs/binfmt_elf.c
    [load_elf_binary]), the default [stack_guard_gap] of 256 pages
    (mm/mmap.c [cmdline_parse_stack_guard_gap]), [vm.mmap_rnd_bits] at
    its riscv64 floor of 18 (arch/riscv/Kconfig), CONFIG_RSEQ on
    (init/Kconfig, default y on riscv64), no vector unit and no cache
    leaf the machine reports (arch/riscv/kernel/cacheinfo.c). *)
Definition witness_kernel : KernelBuild :=
  mkKernelBuild false 0%N false 256%N 0%N true 0%N cache_view_absent.

(** argv ["a"], the one-byte argument of the spec's fixture; the exec
    file name is "a" too ([State.default_execfn]). *)
Definition witness_argv : list (list byte) := [[Z_to_bv 8 97]].

Definition witness_input : ProcInput :=
  mkProcInput_full witness_argv [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1000)
    [] net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false Sv48
    default_urandom [] witness_kernel default_execfn.

(** The launch: the stack VMA ends at STACK_TOP (no draw), sp at the
    top of rule 2 (no [arch_align_stack] pad) and the mmap base of rule
    3 with no draw, which is
    [PAGE_ALIGN(STACK_TOP - max(128 MiB, 8 MiB + 1 MiB))] =
    0x7ffff8000000 (mm/util.c [mmap_base]). *)
Definition witness_top   : word := Z_to_bv 64 0x800000000000.
Definition witness_sp    : word := Z_to_bv 64 0x7ffffffffdf0.
Definition witness_mbase : word := Z_to_bv 64 0x7ffff8000000.

(** The initial break: the page above the one segment of either image
    below, so [Run.valid_brk] holds at its floor. *)
Definition witness_brk : word := Z_to_bv 64 0x1000.

Definition witness_draw : EntryDraw :=
  mkDraw demo_random witness_top vdso_keeps_all.

Definition witness_entry : ExecEntry :=
  mkEntry witness_sp witness_brk witness_mbase witness_draw.

(** The program header table of the spec's fixture: at 0x10040, with
    56-byte entries ([sizeof] of ELF64's program header, the only size
    [load_elf_phdrs] accepts, fs/binfmt_elf.c), four of them. *)
Definition witness_phdrs : PhdrInfo := mkPhdrInfo 0x10040 56 4.

(** The fixture's measurements, as the model computes them, so that the
    bounds below read as the kernel's arithmetic and not as magic
    numbers. *)
Local Lemma witness_va_size : in_va_size witness_input = Sv48.
Proof. reflexivity. Qed.

Local Lemma witness_aslr : kb_aslr (in_kernel witness_input) = false.
Proof. reflexivity. Qed.

Local Lemma witness_L : Z.of_nat
  (launch_string_bytes (in_argv witness_input) (in_envp witness_input)
                       (in_execfn witness_input)) = 4%Z.
Proof. reflexivity. Qed.

Local Lemma witness_C : Z.of_nat
  (block_head_size (kb_rseq (in_kernel witness_input))
                   (in_argv witness_input) (in_envp witness_input)) = 512%Z.
Proof. reflexivity. Qed.

Local Lemma bvu_sp : bv_unsigned witness_sp = 0x7ffffffffdf0%Z.
Proof. reflexivity. Qed.
Local Lemma bvu_brk : bv_unsigned witness_brk = 0x1000%Z.
Proof. reflexivity. Qed.

(* =========================================================================
   What every admitted entry carries
   ========================================================================= *)

(** Rules 1 and 2 of [Run.entry_launch_ok_va], read off a valid entry
    once and in numbers.  Without randomization the stack VMA ends at
    STACK_TOP or one page below it — [load_elf_binary] reads
    [randomize_va_space] once for the draw while [arch_align_stack]
    reads it again, so the pad survives a root write to the sysctl
    during the [execve] — and [create_elf_tables] puts sp between the
    two ends of that pad, a block head below the lowest string. *)
Local Lemma admitted_bounds : forall img en,
  valid_entry img en witness_input ->
  (0x7ffffffff000 <= bv_unsigned (ed_top (en_draw en)) <= 0x800000000000)%Z
  /\ (align_down16 (bv_unsigned (ed_top (en_draw en)) - 8 - 4 - 4095) - 512
      <= bv_unsigned (en_sp en))%Z
  /\ (bv_unsigned (en_sp en)
      <= align_down16 (bv_unsigned (ed_top (en_draw en)) - 8 - 4) - 512)%Z.
Proof.
  intros [segs pc ph] [sp brk mbase draw] Hen.
  unfold valid_entry in Hen. rewrite witness_va_size in Hen.
  cbn [valid_entry_va] in Hen.
  destruct Hen as (_ & _ & _ & _ & Hlaunch).
  cbn [entry_launch_ok_va] in Hlaunch.
  rewrite witness_aslr in Hlaunch.
  destruct Hlaunch as (Htop & Hsp & _).
  destruct Htop as (_ & Hle & Hge).
  destruct Hsp as (_ & Hlo & Hhi).
  unfold launch_sp_lo in Hlo. unfold launch_sp_hi in Hhi.
  rewrite witness_L, witness_C in Hlo. rewrite witness_L, witness_C in Hhi.
  cbn [va_stack_top] in Hle, Hge.
  unfold sp_window_hi, page_size in Hle, Hge.
  cbn [en_draw en_sp].
  split; [lia | split; [exact Hlo | exact Hhi]].
Qed.

(* =========================================================================
   (a) The missing start state
   ========================================================================= *)

(** Linux's address for argv[0] at this launch: [top - 8 - L], with
    L = 4 (the argv string "a" and its NUL, the exec name "a" and ITS
    NUL) and the eight bytes the slot [create_init_stack_vma]
    (mm/vma_exec.c) leaves unwritten at the top of the stack VMA. *)
Definition witness_argv0 : word := Z_to_bv 64 0x7ffffffffff4.

(** THE BYTE CHECK, and the half of A2 (a) that fails before the
    change: the first argv pointer of the block — the eight bytes at
    sp + 8, little-endian — is 0x7ffffffffff4.  Before this change the
    model's block put the strings directly above its own ten-entry
    vector, which put argv[0] 192 bytes above sp, so these eight bytes
    read 0x7ffffffffeb0 and this [Example] was false. *)
Example witness_argv0_pointer :
  firstn 8 (skipn 8 (entry_stack_image witness_input witness_mbase witness_phdrs
                       (Z_to_bv 64 0x10100) witness_sp witness_draw))
  = word_le8 witness_argv0.
Proof. vm_compute. reflexivity. Qed.

(** ... and argv[0] really is 516 bytes above sp here, which is what
    makes the program of the Problem section — abort when
    [argv[0] - sp] is above 0x100 — abort. *)
Example witness_argv0_offset :
  (bv_unsigned witness_argv0 - bv_unsigned witness_sp)%Z = 516%Z.
Proof. vm_compute. reflexivity. Qed.

(** THE STATEMENT ABOUT THE ADMITTED SET, which is what makes A2 (a) a
    claim about the quantifier of every statement and not about one
    entry: at EVERY entry [Run.valid_entry] admits for this input,
    argv[0] is at least 480 bytes above the entry stack pointer.  The
    real distance is at least C = 512 — rule 2 puts sp a whole block
    head below the lowest string — and exactly 516 at the entry above.

    Before this change the model put argv[0] 192 bytes above sp at
    every admitted entry, so the same program was provably
    abort-free. *)
Lemma admitted_argv0_far_above_sp : forall img en,
  valid_entry img en witness_input ->
  (480 <= bv_unsigned (ed_top (en_draw en)) - 8
          - Z.of_nat (launch_string_bytes (in_argv witness_input)
                        (in_envp witness_input) (in_execfn witness_input))
          - bv_unsigned (en_sp en))%Z.
Proof.
  intros img en Hen.
  destruct (admitted_bounds img en Hen) as (_ & _ & Hhi).
  rewrite witness_L.
  unfold align_down16 in Hhi.
  pose proof (Z.mod_pos_bound (bv_unsigned (ed_top (en_draw en)) - 8 - 4) 16
                ltac:(lia)).
  lia.
Qed.

(** The same bound on the address the model itself computes for
    argv[0], [StackLayout.string_base_addr], so that the statement is
    about the pointer the block carries rather than a rewriting of it.
    The subtraction does not wrap: rule 1 keeps the stack top within a
    page of STACK_TOP. *)
Lemma admitted_string_base : forall img en,
  valid_entry img en witness_input ->
  bv_unsigned (string_base_addr (ed_top (en_draw en)) (in_argv witness_input)
                 (in_envp witness_input) (in_execfn witness_input))
  = (bv_unsigned (ed_top (en_draw en)) - 12)%Z.
Proof.
  intros img en Hen.
  destruct (admitted_bounds img en Hen) as ((Hge & Hle) & _ & _).
  unfold string_base_addr.
  assert (H12 : bv_unsigned (nat_to_word
                   (8 + launch_string_bytes (in_argv witness_input)
                          (in_envp witness_input) (in_execfn witness_input)))
                = 12%Z) by reflexivity.
  rewrite bv_sub_unsigned, H12.
  apply bv_wrap_small.
  change (bv_modulus 64) with (2 ^ 64)%Z. lia.
Qed.

Lemma admitted_string_base_far_above_sp : forall img en,
  valid_entry img en witness_input ->
  (480 <= bv_unsigned (string_base_addr (ed_top (en_draw en))
                         (in_argv witness_input) (in_envp witness_input)
                         (in_execfn witness_input))
          - bv_unsigned (en_sp en))%Z.
Proof.
  intros img en Hen.
  rewrite (admitted_string_base img en Hen).
  pose proof (admitted_argv0_far_above_sp img en Hen) as H.
  rewrite witness_L in H. lia.
Qed.

(* =========================================================================
   Stepping a straight-line image
   ========================================================================= *)

(** Two devices, and both are forced.

    THE STACK MEMORY IS A VARIABLE.  The entry stack image is a
    function of sp, so a [vm_compute] that had to look at it could not
    run at a quantified entry.  None of the instructions below touches
    memory until the faulting load, so the memory is a variable
    everywhere except there.

    EACH INTERMEDIATE STATE IS WRITTEN FLAT.  [RiscvSemantics.set_reg]
    rebuilds the machine state from eight projections of its argument,
    so a term for the state after n instructions holds 8^n copies of
    the state before them and the kernel does not share them: a
    conversion check over the state after three instructions of this
    image takes 98 seconds, and over the state after four it does not
    finish.  So every state below is a record literal whose fields are
    written out, and each step lemma relates two such literals. *)

Local Definition img_rom (segs : list Segment) : word -> option byte :=
  fun addr =>
    match memory_read segs addr 1 with
    | Some (b :: _) => Some b
    | _ => None
    end.

(** [Run.init_machine_state] with the memory named: every other field
    is a literal of that definition, so the bridge below is a
    conversion. *)
Local Definition start_state (segs : list Segment) (pc : N) (sp : word)
    (mem : word -> option byte) : machine_state :=
  {| ms_regs := bvmap_set 2 sp (bvmap_set 10 (Z_to_bv 64 0) bvmap_empty);
     ms_fregs := bvmap_empty;
     ms_pc_val := Z_to_bv 64 (Z.of_N pc);
     ms_svc_pending := None;
     ms_resv := None;
     ms_fcsr := Z_to_bv 32 0;
     ms_mem := mem;
     ms_rom := img_rom segs |}.

Local Lemma start_state_init : forall segs pc ph sp mbase draw inp,
  init_machine_state segs pc ph sp mbase draw inp
  = start_state segs pc sp
      (ms_mem (init_machine_state segs pc ph sp mbase draw inp)).
Proof. intros. reflexivity. Qed.

(** The same state with t0 (x5) loaded and the program counter at [pc].
    Every state of either image after its first instruction has this
    shape. *)
Local Definition probe_state (segs : list Segment) (sp t0 : word) (pc : Z)
    (mem : word -> option byte) : machine_state :=
  {| ms_regs := bvmap_set 5 t0
                  (bvmap_set 2 sp (bvmap_set 10 (Z_to_bv 64 0) bvmap_empty));
     ms_fregs := bvmap_empty;
     ms_pc_val := Z_to_bv 64 pc;
     ms_svc_pending := None;
     ms_resv := None;
     ms_fcsr := Z_to_bv 32 0;
     ms_mem := mem;
     ms_rom := img_rom segs |}.

(** From a configuration whose instruction step is a function answer,
    the only transition is that step, silently; when the answer is a
    fault, the error transition is the one available.  The same facts
    as [Checks.Omni]'s [sstep_instr_only] and [sstep_fault_only],
    restated here because that file is not a dependency of this one. *)
Local Lemma istep_only : forall segs ms model ms',
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  forall evs st, sstep segs (mkCfg ms model) evs st ->
    evs = [] /\ st = SNext (mkCfg ms' model).
Proof.
  intros segs ms model ms' Hlazy Hsvc Hstep evs st Hss.
  inversion Hss; subst;
    try (match goal with
         | H : mi_account_step _ _ _ = _ |- _ =>
             rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep in H;
             first [ inversion H; subst; split; reflexivity | discriminate H ]
         end);
    congruence.
Qed.

Local Lemma istep : forall segs ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sstep segs (mkCfg ms model) [] (SNext (mkCfg ms' model)).
Proof.
  intros segs ms model ms' Hh Hlazy Hsvc Hstep.
  apply sstep_instr; [exact Hh | exact Hsvc |].
  rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Local Lemma istep_fault : forall segs ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineFault ->
  sstep segs (mkCfg ms model) [] SError.
Proof.
  intros segs ms model Hh Hlazy Hsvc Hstep.
  apply sstep_instr_fault; [exact Hh | exact Hsvc |].
  rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Local Lemma star_silent : forall segs c1 c2 c3,
  sstep segs c1 [] (SNext c2) -> star segs c2 [] c3 -> star segs c1 [] c3.
Proof.
  intros segs c1 c2 c3 H1 H2.
  change ([] : list event) with (([] : list event) ++ ([] : list event)).
  eapply star_step; [exact H1 | exact H2].
Qed.

(* =========================================================================
   (b) The extra start state: two images that watch the stack pointer
   ========================================================================= *)

(** Both images have the same six-instruction shape: build a 47-bit
    constant in t0, compare it with sp, and either spin on a
    self-branch or load from address 0, which no launch maps.

      0x100  lui  t0, HI          b7 02 .. ..
      0x104  addi t0, t0, LO      93 82 f2 ..
      0x108  slli t0, t0, SH      93 92 .. 01
      0x10c  bgeu A, B, 0x114     63 .. .. 00
      0x110  ld   t1, 0(x0)       03 33 00 00
      0x114  jal  x0, 0           6f 00 00 00

    [low_image] takes A = sp and B = t0, so it reaches the load exactly
    when sp is BELOW the constant; [high_image] takes A = t0 and
    B = sp, so it reaches the load exactly when sp is ABOVE it.
    [jal x0, 0] is a fixed point of the machine: the link-register
    write is dropped ([RiscvSemantics.set_reg] discards writes to x0)
    and the jump target is the instruction itself. *)

(** 0x7fffbf000000 = (0x800000 - 65) shifted left by 24.  It is below
    every stack pointer Linux gives for this input and above
    [State.sp_window_lo] = 0x7fff80000000, the floor the model used to
    admit. *)
Definition low_threshold : word := Z_to_bv 64 0x7fffbf000000.

(** 0x7fffffc00000 = (0x2000000 - 1) shifted left by 22: 4 MiB below
    STACK_TOP, so every launch of this input without randomization
    stands above it. *)
Definition high_threshold : word := Z_to_bv 64 0x7fffffc00000.

Local Lemma bvu_low : bv_unsigned low_threshold = 0x7fffbf000000%Z.
Proof. reflexivity. Qed.

Definition low_segment : Segment := {|
  seg_base  := 0x100;
  seg_size  := 24;
  seg_perms := "r-x"%string;
  seg_bytes := ["b70280009382f2fb9392820163745100033300006f000000"%pstring]
|}.
Definition low_segments : list Segment := [low_segment].
Definition low_image : Image := mkImage low_segments 0x100 witness_phdrs.

Definition high_segment : Segment := {|
  seg_base  := 0x100;
  seg_size  := 24;
  seg_perms := "r-x"%string;
  seg_bytes := ["b70200029382f2ff9392620163f42200033300006f000000"%pstring]
|}.
Definition high_segments : list Segment := [high_segment].
Definition high_image : Image := mkImage high_segments 0x100 witness_phdrs.

(* ---- the image that faults on a LOW stack pointer ---------------------- *)

(** The five states of a run that does NOT fault: the entry, the three
    states of the constant being built (0x800000, then 0x7fffbf, then
    0x7fffbf000000), and the self-branch at 0x114. *)
Local Definition low_s0 (sp : word) (mem : word -> option byte) : machine_state :=
  start_state low_segments 0x100 sp mem.
Local Definition low_s1 (sp : word) (mem : word -> option byte) : machine_state :=
  probe_state low_segments sp (Z_to_bv 64 0x800000) 0x104 mem.
Local Definition low_s2 (sp : word) (mem : word -> option byte) : machine_state :=
  probe_state low_segments sp (Z_to_bv 64 0x7fffbf) 0x108 mem.
Local Definition low_s3 (sp : word) (mem : word -> option byte) : machine_state :=
  probe_state low_segments sp low_threshold 0x10c mem.
Local Definition low_s4 (sp : word) (mem : word -> option byte) : machine_state :=
  probe_state low_segments sp low_threshold 0x114 mem.

Local Lemma low_step0 : forall sp mem,
  RiscvSemantics.step low_segments (low_s0 sp mem) = MachineOk (low_s1 sp mem).
Proof. intros. vm_compute. reflexivity. Qed.

Local Lemma low_step1 : forall sp mem,
  RiscvSemantics.step low_segments (low_s1 sp mem) = MachineOk (low_s2 sp mem).
Proof. intros. vm_compute. reflexivity. Qed.

Local Lemma low_step2 : forall sp mem,
  RiscvSemantics.step low_segments (low_s2 sp mem) = MachineOk (low_s3 sp mem).
Proof. intros. vm_compute. reflexivity. Qed.

(** THE BRANCH.  With sp at or above the constant it is taken, and the
    load at 0x110 is never reached. *)
Local Lemma low_step3 : forall sp mem,
  bv_ltu sp low_threshold = false ->
  RiscvSemantics.step low_segments (low_s3 sp mem) = MachineOk (low_s4 sp mem).
Proof.
  intros sp mem Hb. vm_compute in Hb |- *. rewrite Hb. reflexivity.
Qed.

(** ... and the self-branch is a fixed point. *)
Local Lemma low_step4 : forall sp mem,
  RiscvSemantics.step low_segments (low_s4 sp mem) = MachineOk (low_s4 sp mem).
Proof. intros. vm_compute. reflexivity. Qed.

Local Definition low_inv (sp : word) (mem : word -> option byte)
    (model : Model) (c : config) : Prop :=
  c = mkCfg (low_s0 sp mem) model \/ c = mkCfg (low_s1 sp mem) model
  \/ c = mkCfg (low_s2 sp mem) model \/ c = mkCfg (low_s3 sp mem) model
  \/ c = mkCfg (low_s4 sp mem) model.

(** Every transition out of a reachable configuration goes to another
    reachable one, and none of them is the error transition. *)
Local Lemma low_inv_sstep : forall sp mem model,
  m_vm_lazy model = [] ->
  bv_ltu sp low_threshold = false ->
  forall c evs st, low_inv sp mem model c -> sstep low_segments c evs st ->
    exists c', st = SNext c' /\ low_inv sp mem model c'.
Proof.
  intros sp mem model Hlazy Hb c evs st Hinv Hss.
  destruct Hinv as [-> | [-> | [-> | [-> | ->]]]].
  - destruct (istep_only low_segments _ model _ Hlazy eq_refl
                (low_step0 sp mem) _ _ Hss) as (_ & ->).
    eexists. split; [reflexivity | right; left; reflexivity].
  - destruct (istep_only low_segments _ model _ Hlazy eq_refl
                (low_step1 sp mem) _ _ Hss) as (_ & ->).
    eexists. split; [reflexivity | right; right; left; reflexivity].
  - destruct (istep_only low_segments _ model _ Hlazy eq_refl
                (low_step2 sp mem) _ _ Hss) as (_ & ->).
    eexists. split; [reflexivity | right; right; right; left; reflexivity].
  - destruct (istep_only low_segments _ model _ Hlazy eq_refl
                (low_step3 sp mem Hb) _ _ Hss) as (_ & ->).
    eexists. split; [reflexivity | right; right; right; right; reflexivity].
  - destruct (istep_only low_segments _ model _ Hlazy eq_refl
                (low_step4 sp mem) _ _ Hss) as (_ & ->).
    eexists. split; [reflexivity | right; right; right; right; reflexivity].
Qed.

Local Lemma low_no_error_mem : forall sp mem model,
  m_vm_lazy model = [] ->
  bv_ltu sp low_threshold = false ->
  ~ reaches_error low_segments (mkCfg (low_s0 sp mem) model).
Proof.
  intros sp mem model Hlazy Hb (tr & c & evs & Hstar & Herr).
  assert (Hpres : forall c0 e c', low_inv sp mem model c0 ->
                    sstep low_segments c0 e (SNext c') -> low_inv sp mem model c').
  { intros c0 e c' Hi Hs.
    destruct (low_inv_sstep sp mem model Hlazy Hb c0 e (SNext c') Hi Hs)
      as (c'' & Heq & Hi'). injection Heq as ->. exact Hi'. }
  pose proof (star_invariant low_segments (low_inv sp mem model) Hpres
                _ _ _ Hstar (or_introl eq_refl)) as Hc.
  destruct (low_inv_sstep sp mem model Hlazy Hb c evs SError Hc Herr)
    as (c' & Habs & _).
  discriminate Habs.
Qed.

(** THE LOWER BOUND ON THE ADMITTED STACK POINTERS, the whole of what
    rules 1 and 2 buy here: the stack VMA ends at STACK_TOP or one page
    below, and [create_elf_tables] (fs/binfmt_elf.c) puts sp at most
    [4095 + 15 + 8 + L + C] below that end.  So the lowest admitted
    stack pointer is 0x7fffffffddf0, nowhere near 0x7fffbf000000.
    Before this change [Run.valid_sp] alone admitted
    [State.sp_window_lo] = 0x7fff80000000, which is below it. *)
Local Lemma admitted_sp_high : forall img en,
  valid_entry img en witness_input ->
  bv_ltu (en_sp en) low_threshold = false.
Proof.
  intros img en Hen.
  destruct (admitted_bounds img en Hen) as ((Hge & _) & Hlo & _).
  unfold align_down16 in Hlo.
  pose proof (Z.mod_pos_bound
                (bv_unsigned (ed_top (en_draw en)) - 8 - 4 - 4095) 16
                ltac:(lia)).
  unfold bv_ltu. rewrite bvu_low.
  apply Z.ltb_ge. lia.
Qed.

(** THE FIRST HALF OF THE REFUTATION: at every entry the model admits
    for this input, [low_image] spins forever and never reaches its
    load.  Before this change the entry with sp = 0x7fff80000000 was
    admitted and this theorem was false. *)
Theorem low_image_error_free : forall lim en,
  valid_entry low_image en witness_input ->
  ~ bh_errors (run low_image lim en witness_input).
Proof.
  intros lim en Hen.
  pose proof (admitted_sp_high low_image en Hen) as Hb.
  destruct en as [sp brk mbase draw]. cbn [en_sp] in Hb.
  unfold low_image. cbn [run bh_errors]. unfold init_config.
  rewrite (start_state_init low_segments 0x100 witness_phdrs sp mbase draw
             witness_input).
  apply low_no_error_mem; [reflexivity | exact Hb].
Qed.

(* ---- the image that faults on a HIGH stack pointer --------------------- *)

Local Definition high_s0 (sp : word) (mem : word -> option byte) : machine_state :=
  start_state high_segments 0x100 sp mem.
Local Definition high_s1 (sp : word) (mem : word -> option byte) : machine_state :=
  probe_state high_segments sp (Z_to_bv 64 0x2000000) 0x104 mem.
Local Definition high_s2 (sp : word) (mem : word -> option byte) : machine_state :=
  probe_state high_segments sp (Z_to_bv 64 0x1ffffff) 0x108 mem.
Local Definition high_s3 (sp : word) (mem : word -> option byte) : machine_state :=
  probe_state high_segments sp high_threshold 0x10c mem.

(** The load at 0x110, which the branch falls through to when sp is
    above the constant. *)
Local Definition high_s4 (sp : word) (mem : word -> option byte) : machine_state :=
  probe_state high_segments sp high_threshold 0x110 mem.

Local Lemma high_step0 : forall sp mem,
  RiscvSemantics.step high_segments (high_s0 sp mem) = MachineOk (high_s1 sp mem).
Proof. intros. vm_compute. reflexivity. Qed.

Local Lemma high_step1 : forall sp mem,
  RiscvSemantics.step high_segments (high_s1 sp mem) = MachineOk (high_s2 sp mem).
Proof. intros. vm_compute. reflexivity. Qed.

Local Lemma high_step2 : forall sp mem,
  RiscvSemantics.step high_segments (high_s2 sp mem) = MachineOk (high_s3 sp mem).
Proof. intros. vm_compute. reflexivity. Qed.

(** At the witness entry sp is 0x7ffffffffdf0, above the constant, so
    the branch is NOT taken and the next instruction is the load. *)
Local Lemma high_step3 : forall mem,
  RiscvSemantics.step high_segments (high_s3 witness_sp mem)
  = MachineOk (high_s4 witness_sp mem).
Proof. intros. vm_compute. reflexivity. Qed.

(** The memory of the witness launch: the 528-byte entry block at sp
    and the zeroed stack window below it.  Address 0 is in neither, and
    the image's one segment starts at 0x100, so the load faults. *)
Local Definition high_mem : word -> option byte :=
  ms_mem (init_machine_state high_segments 0x100 witness_phdrs witness_sp
            witness_mbase witness_draw witness_input).

(** The stack window's floor is [max(ed_top - 8 MiB, base + guard gap)]
    (mm/vma.c [acct_stack_growth] and [expand_downwards]), so nothing
    maps the first page and the model takes the fault transition. *)
Local Lemma high_fault :
  RiscvSemantics.step high_segments (high_s4 witness_sp high_mem) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

Local Definition high_model (lim : Z) : Model :=
  init_model (segments_reserved high_segments) witness_brk witness_mbase
             witness_sp lim witness_input.

Local Lemma high_reaches_error : forall lim,
  reaches_error high_segments
    (mkCfg (high_s0 witness_sp high_mem) (high_model lim)).
Proof.
  intros lim.
  exists [], (mkCfg (high_s4 witness_sp high_mem) (high_model lim)), [].
  split.
  - eapply star_silent;
      [ exact (istep high_segments _ (high_model lim) _ eq_refl eq_refl eq_refl
                 (high_step0 witness_sp high_mem)) |].
    eapply star_silent;
      [ exact (istep high_segments _ (high_model lim) _ eq_refl eq_refl eq_refl
                 (high_step1 witness_sp high_mem)) |].
    eapply star_silent;
      [ exact (istep high_segments _ (high_model lim) _ eq_refl eq_refl eq_refl
                 (high_step2 witness_sp high_mem)) |].
    eapply star_silent;
      [ exact (istep high_segments _ (high_model lim) _ eq_refl eq_refl eq_refl
                 (high_step3 high_mem)) |].
    apply star_refl.
  - exact (istep_fault high_segments _ (high_model lim) eq_refl eq_refl eq_refl
             high_fault).
Qed.

(** THE SECOND HALF: [high_image] faults at the witness entry, the
    launch A4's [norandmaps] boot records. *)
Theorem high_image_errors_at_witness : forall lim,
  bh_errors (run high_image lim witness_entry witness_input).
Proof.
  intros lim.
  unfold high_image, witness_entry. cbn [run bh_errors]. unfold init_config.
  rewrite (start_state_init high_segments 0x100 witness_phdrs witness_sp
             witness_mbase witness_draw witness_input).
  exact (high_reaches_error lim).
Qed.

(* ---- the witness entry is admitted ------------------------------------- *)

(** The start state of A1's fixture without randomization: stack top at
    STACK_TOP, sp = 0x7ffffffffdf0, mmap base 0x7ffff8000000.  Stated
    for any image, because the refutation needs an entry of each. *)
Local Lemma witness_entry_admitted_for : forall segs pc ph,
  valid_brk segs witness_brk ->
  valid_entry (mkImage segs pc ph) witness_entry witness_input.
Proof.
  intros segs pc ph Hbrk.
  unfold valid_entry. rewrite witness_va_size.
  unfold witness_entry. cbn [valid_entry_va].
  split; [| split; [exact Hbrk | split; [| split]]].
  - unfold valid_sp_va.
    split; [vm_compute; discriminate
           | split; [vm_compute; discriminate | vm_compute; reflexivity]].
  - unfold valid_mmap_base_va.
    split; [vm_compute; discriminate
           | split; [vm_compute; discriminate | vm_compute; reflexivity]].
  - unfold entry_stack_fits_va. vm_compute. discriminate.
  - cbn [entry_launch_ok_va]. split; [| split].
    + unfold valid_stack_top_va.
      split; [vm_compute; reflexivity
             | split; [vm_compute; discriminate | vm_compute; discriminate]].
    + unfold valid_launch_sp.
      split; [vm_compute; reflexivity
             | split; [vm_compute; discriminate | vm_compute; discriminate]].
    + exists 0%Z.
      split; [lia |].
      split; [intros Hc; discriminate Hc |].
      split; [intros _; reflexivity |].
      vm_compute. reflexivity.
Qed.

Lemma witness_entry_admitted_low :
  valid_entry low_image witness_entry witness_input.
Proof.
  unfold low_image. apply witness_entry_admitted_for.
  unfold valid_brk. rewrite bvu_brk.
  split; [vm_compute; discriminate
         | split; [vm_compute; discriminate | reflexivity]].
Qed.

Lemma witness_entry_admitted_high :
  valid_entry high_image witness_entry witness_input.
Proof.
  unfold high_image. apply witness_entry_admitted_for.
  unfold valid_brk. rewrite bvu_brk.
  split; [vm_compute; discriminate
         | split; [vm_compute; discriminate | reflexivity]].
Qed.

(* ---- the refutation ----------------------------------------------------- *)

(** A2 (b).  [Classifier.agree] asks, among other things, that one
    image may fault at some admitted entry exactly when the other may.
    [high_image] faults at the witness entry; [low_image] faults at
    none; so the two sides of that conjunct differ and [agree] is
    false.  The budget is [Classifier.classifier_alloc_limit], the one
    every other [Classifier] statement runs at.

    Before this change the model admitted sp = 0x7fff80000000, where
    [low_image] faults too, and this theorem was false: [agree] held
    there, of a pair of programs that disagree on Linux. *)
Theorem refutes_agree :
  ~ Classifier.agree low_image high_image Classifier.classifier_alloc_limit
      witness_input.
Proof.
  intros (_ & Herrs & _ & _).
  destruct (proj2 Herrs
              (ex_intro _ witness_entry
                 (conj witness_entry_admitted_high
                    (high_image_errors_at_witness
                       Classifier.classifier_alloc_limit))))
    as (en & Hen & Herr).
  exact (low_image_error_free Classifier.classifier_alloc_limit en Hen Herr).
Qed.
