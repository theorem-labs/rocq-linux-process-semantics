(** * LinuxProcessSem.Checks.Cases.Mm.StackVma — the stack as a ledger entry, pinned on a real launch

    The stack is a [vm_reserved] entry ([State.stack_reserved]): the
    window [[Run.stack_window_lo, ed_top)] the start state maps for it,
    at its full [RLIMIT_STACK] size.  Below it is the guard band
    [State.stack_guard_band], which a hint, both placement windows and
    [brk] keep free and which MAP_FIXED and an in-place [mremap] do not
    (Linux v6.18.46, commit 1f99e9ab748f: [vm_start_gap] in
    include/linux/mm.h is read by [generic_get_unmapped_area_topdown]
    and [unmapped_area] but not by the MAP_FIXED return of
    [__get_unmapped_area] nor by [vma_expandable] in mm/mremap.c).

    Every case runs [Checks.ExecutableSpecs.check_syscall_for_run] from
    the start model of a launch [Run.valid_entry] accepts, built by
    [Run.init_config] from the image, the entry and the input, so none
    of them rests on a hand-built ledger.

    THE FIVE CASES.
    - D3, the defect: an in-place [mremap] grow up to the stack's floor
      is accepted ([d3_mremap_inplace_accepted]).  It used to be
      rejected, because the model bounded every grow by [alloc_top].
    - D3's control, the same effect two pages lower
      ([d3_control_inplace_accepted]).
    - The residual R-e: D3's own first call, a hinted [mmap] just below
      the stack's floor, is refused ([residual_hint_below_full_stack_refused]).
    - R-b closed: a hint above the stack, below [TASK_SIZE], is honoured
      ([rb_hint_above_stack_honoured]).
    - R-c closed: a hint inside the guard band is refused, and one page
      lower it is honoured ([rc_hint_in_guard_band_refused],
      [rc_hint_below_guard_band_honoured]). *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs Placement.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The launch: one argument of 7660 'x' bytes, no environment, the default
   kernel with randomisation off, Sv48.  The entry block is 8 KiB, so
   sp = 0x7fffffffe000 and the stack VMA ends at STACK_TOP = 2^47.
   ========================================================================= *)

Definition sv_argv : list (list byte) := [repeat (Z_to_bv 8 120) 7660].

(** [State.default_kernel] with [kb_aslr] (the third field) false. *)
Definition sv_kernel : KernelBuild :=
  mkKernelBuild false 1%N false 256%N 0%N true 0%N cache_view_absent.

Definition sv_input : ProcInput :=
  mkProcInput_full sv_argv [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48
    default_urandom [] sv_kernel default_execfn true true.

Lemma sv_argv_valid : valid_argv sv_argv.
Proof.
  unfold valid_argv, sv_argv.
  split; [split; apply Z.leb_le; vm_compute; reflexivity |].
  split; [apply Z.leb_le; vm_compute; reflexivity |].
  split; [constructor; [apply Z.leb_le; vm_compute; reflexivity | constructor] |].
  split.
  - constructor; [| constructor].
    intro H. apply repeat_spec in H. apply (f_equal bv_unsigned) in H.
    vm_compute in H. discriminate.
  - constructor.
Qed.

Lemma sv_input_valid : valid_input sv_input.
Proof.
  unfold valid_input.
  split; [exact sv_argv_valid |].
  unfold valid_envp.
  unfold sv_input. cbn [in_argv in_envp in_fs].
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try (unfold valid_hwcap; left; reflexivity);
    try (unfold fs_image_real; vm_compute; reflexivity);
    try (unfold valid_launch; split;
         [ unfold valid_execfn, valid_path_name, default_execfn; left; split;
           [ cbn; lia
           | cbn; intros [Hz | []]; apply (f_equal bv_unsigned) in Hz;
             vm_compute in Hz; discriminate ]
         | unfold e2big_limit; apply Z.leb_le; vm_compute; reflexivity ]);
    try (unfold valid_execfn, valid_path_name, default_execfn; left; split;
         [ cbn; lia
         | cbn; intros [Hz | []]; apply (f_equal bv_unsigned) in Hz;
           vm_compute in Hz; discriminate ]);
    try (unfold e2big_limit, launch_bytes; apply Z.leb_le; vm_compute; reflexivity);
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | split
                 | cbn; lia | reflexivity | intros [] ].
  all: try valid_urandom_default.
Qed.

(** The image: [Checks.Examples.exit0_image]'s one segment. *)
Definition sv_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 12;
  seg_perms := "r-x"%string;
  seg_bytes := ["9308d0051305000073000000"%pstring];
  seg_kind  := SegLoader
|}.
Definition sv_segs : list Segment := [sv_segment].
Definition sv_image : Image := mkImage sv_segs 0x100 demo_phdrs.

Definition sv_entry : ExecEntry :=
  launch_entry_va Sv48 sv_input (Z_to_bv 64 0x1000) demo_random vdso_keeps_all.

Lemma sv_entry_valid : valid_entry sv_image sv_entry sv_input.
Proof.
  pose proof sv_input_valid as Hvalid.
  red in Hvalid.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  unfold valid_entry, sv_entry, sv_image.
  change (in_va_size sv_input) with Sv48.
  apply launch_entry_va_valid; try assumption.
  unfold valid_brk.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  repeat split; try lia; vm_compute; try reflexivity; try discriminate.
Qed.

(** The launch the entry encodes: stack top, sp, break, mmap base. *)
Definition sv_fields (en : ExecEntry) : Z * Z * Z * Z :=
  match en with
  | mkEntry sp brk mb draw =>
      (bv_unsigned (ed_top draw), bv_unsigned sp, bv_unsigned brk, bv_unsigned mb)
  end.

Example sv_fields_are :
  sv_fields sv_entry = (0x800000000000, 0x7fffffffe000, 0x1000, 0x7ffff8000000)%Z.
Proof. vm_compute. reflexivity. Qed.

(** The start model: exactly the model of the configuration [Run.run]
    starts from for (sv_image, source_alloc_limit, en, sv_input). *)
Definition start_of (en : ExecEntry) : Model :=
  match sv_image, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      cfg_model (init_config segs pc ph sp brk0 mbase rnd source_alloc_limit sv_input)
  end.

Definition sv_start : Model := start_of sv_entry.

(** THE LEDGER.  The stack's entry is [[0x7fffff800000, 2^47)]: 8 MiB
    below the stack VMA's end, above the base plus the guard gap.  The
    guard band below it is [[0x7fffff700000, 0x7fffff800000)], 256
    pages.  [alloc_top] is 0x7fffff7fe000, inside the band, which is
    why the old model's [alloc_top] gates differed from Linux both
    ways. *)
Example sv_stack_entry :
  stack_reserved (m_kernel sv_start) (vm_mmap_base (m_vmmaps sv_start))
    0x800000000000
  = [ (Z_to_bv 64 0x7fffff800000, Z_to_bv 64 0x800000) ]
  /\ map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p)))
       (stack_guard_band (m_kernel sv_start) (m_vmmaps sv_start))
     = [ (0x7fffff700000, 0x100000)%Z ]
  /\ alloc_top (m_vmmaps sv_start) = 0x7fffff7fe000%Z.
Proof. split; [check_eq | split; vm_compute; reflexivity]. Qed.

(* =========================================================================
   The calls and their verdicts
   ========================================================================= *)

Inductive outcome :=
| OOk (ret : Z) (maps : list (Z * Z))
| OReject
| OUnmodeled
| ORunError.

Definition summarize (eff : SyscallEffect) (r : option check_result) : outcome :=
  match r with
  | Some (CheckOk m _) =>
      OOk (bv_unsigned (eff_ret eff))
          (map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p)))
               (vm_maps (m_vmmaps m)))
  | Some CheckReject => OReject
  | Some CheckUnmodeled => OUnmodeled
  | None => ORunError
  end.

Definition model_of (r : option check_result) (m0 : Model) : Model :=
  match r with Some (CheckOk m _) => m | _ => m0 end.

(** [mmap(a, 4096, PROT_READ|PROT_WRITE, flags, -1, 0)] and Linux's
    answer when it maps [a]. *)
Definition mmap_in (a flags : Z) : SyscallInput :=
  mkInput 222 [Z_to_bv 64 a; 4096; 3; Z_to_bv 64 flags; Z_to_bv 64 (-1); 0]
    (fun _ => None) (fun _ => None).
Definition mmap_at (a : Z) : SyscallEffect :=
  mkEffect (Z_to_bv 64 a) [] [(Z_to_bv 64 a, 4096)].

(** MAP_PRIVATE | MAP_ANONYMOUS, and the same with MAP_FIXED_NOREPLACE. *)
Definition f_hint : Z := 0x22%Z.
Definition f_noreplace : Z := 0x100022%Z.

(** [mremap(a, 4096, 8192, MREMAP_MAYMOVE)], and Linux's in-place
    answer: the tail [[a + 4096, a + 8192)] zero-filled, [a] returned. *)
Definition mremap_in (a : Z) : SyscallInput :=
  mkInput 216 [Z_to_bv 64 a; 4096; 8192; 1; 0; 0] (fun _ => None) (fun _ => None).
Definition mremap_inplace (a : Z) : SyscallEffect :=
  mkEffectU (Z_to_bv 64 a) [] [(Z_to_bv 64 (a + 4096), 4096)] [] [] [].

(** D3's address: the page whose 8 KiB grow ends exactly at the stack's
    floor, 0x7fffff800000 - 0x1000. *)
Definition g : Z := 0x7fffff7fd000%Z.

(* -------------------------------------------------------------------------
   Case 1, D3.  The mapping is made with MAP_FIXED_NOREPLACE at [g]:
   Linux keeps no guard gap on that path, so it maps [g] whatever the
   stack's size, and so does the model.  Then the grow.  [g + 8192] is
   the stack's floor: the grown range meets neither the stack nor
   anything else, and Linux grows in place ([vma_expandable] tests only
   [find_vma_intersection], mm/mremap.c).  The model used to answer this
   with a move, because [alloc_top] ([g + 4096]) bounded every grow.
   ------------------------------------------------------------------------- *)

Definition d3_map := check_syscall_for_run (mmap_in g f_noreplace) (mmap_at g) sv_start.

Example d3_noreplace_map_accepted :
  summarize (mmap_at g) d3_map = OOk g [(g, 4096%Z)].
Proof. vm_compute. reflexivity. Qed.

Example d3_mremap_inplace_accepted :
  summarize (mremap_inplace g)
    (check_syscall_for_run (mremap_in g) (mremap_inplace g) (model_of d3_map sv_start))
  = OOk g [(g, 8192%Z)].
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------
   Case 2, D3's control: the same two calls two pages lower.
   ------------------------------------------------------------------------- *)

Definition g2 : Z := (g - 8192)%Z.

Definition d3c_map := check_syscall_for_run (mmap_in g2 f_noreplace) (mmap_at g2) sv_start.

Example d3_control_inplace_accepted :
  summarize (mmap_at g2) d3c_map = OOk g2 [(g2, 4096%Z)]
  /\ summarize (mremap_inplace g2)
       (check_syscall_for_run (mremap_in g2) (mremap_inplace g2)
          (model_of d3c_map sv_start))
     = OOk g2 [(g2, 8192%Z)].
Proof. split; vm_compute; reflexivity. Qed.

(* -------------------------------------------------------------------------
   Case 3, THE RESIDUAL R-e.  D3's original first call: a HINTED mmap at
   [g].  Linux honours it: at entry its stack VMA is the entry image
   plus 128 KiB ([setup_arg_pages], fs/exec.c), near 2^47, and its guard
   gap is far above [g].  The model refuses it, because its stack entry
   is the stack at its full [RLIMIT_STACK] size and [g] lies inside the
   guard band below that.  SCOPE.md names this residual.

   THIS VERDICT FLIPS IF FAULT-DRIVEN STACK GROWTH IS EVER ADDED.  A model
   whose stack entry starts at Linux's current VMA and grows on a fault
   ([expand_downwards], mm/vma.c) honours this hint, and then this case
   must change to [OOk g [(g, 4096)]] in the same commit that removes
   the residual from SCOPE.md.
   ------------------------------------------------------------------------- *)

Example residual_hint_below_full_stack_refused :
  summarize (mmap_at g) (check_syscall_for_run (mmap_in g f_hint) (mmap_at g) sv_start)
  = OReject.
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------
   Case 5, R-c CLOSED: a hint inside the guard band is refused, and one
   page below the band it is honoured.  The refused one is the band's
   lowest page, [0x7fffff700000], which the old model honoured: it is
   below [alloc_top].  Linux refuses it too once its stack has grown to
   the [RLIMIT_STACK] extent, the case R-c named; at entry the residual
   above applies.
   ------------------------------------------------------------------------- *)

Definition rc_in : Z := 0x7fffff700000%Z.
Definition rc_below : Z := (rc_in - 4096)%Z.

Example rc_hint_in_guard_band_refused :
  summarize (mmap_at rc_in)
    (check_syscall_for_run (mmap_in rc_in f_hint) (mmap_at rc_in) sv_start)
  = OReject.
Proof. vm_compute. reflexivity. Qed.

Example rc_hint_below_guard_band_honoured :
  summarize (mmap_at rc_below)
    (check_syscall_for_run (mmap_in rc_below f_hint) (mmap_at rc_below) sv_start)
  = OOk rc_below [(rc_below, 4096%Z)].
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   Case 4, R-b CLOSED: a launch whose stack VMA ends a page below 2^47,
   and a hint in that page.

   [arch_align_stack] (arch/riscv/kernel/process.c) subtracts up to a
   page from the stack top even with randomisation off, so the stack VMA
   can end at STACK_TOP - 4096 ([Run.valid_stack_top_va]).  The page
   [[STACK_TOP - 4096, STACK_TOP)] is then free and below [mmap_end] =
   [TASK_SIZE], and Linux honours a hint there.  The old model refused
   it: the hint was above [alloc_top].
   ========================================================================= *)

Definition rb_top : word := Z_to_bv 64 (va_stack_top Sv48 - 4096).

Definition rb_entry : ExecEntry :=
  mkEntry (Z_to_bv 64 (launch_sp_hi rb_top sv_input))
          (Z_to_bv 64 0x1000)
          (Z_to_bv 64 (mmap_base_of Sv48 (in_kernel sv_input) 0))
          (mkDraw demo_random rb_top vdso_keeps_all).

Ltac sv_arith :=
  repeat split;
  first [ reflexivity | discriminate | (intros H; discriminate H)
        | (intros; reflexivity) | lia ].

Lemma rb_entry_launch_ok : entry_launch_ok_va Sv48 rb_entry sv_input.
Proof.
  unfold entry_launch_ok_va, rb_entry. cbn [ed_top].
  split; [|split].
  - unfold valid_stack_top_va. vm_compute. sv_arith.
  - unfold valid_launch_sp. vm_compute. sv_arith.
  - exists 0%Z. vm_compute. sv_arith.
Qed.

Lemma rb_entry_valid : valid_entry sv_image rb_entry sv_input.
Proof.
  pose proof sv_input_valid as Hvalid.
  red in Hvalid.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  pose proof rb_entry_launch_ok as Hok.
  assert (Hl : valid_launch sv_input) by assumption.
  unfold valid_entry, sv_image. change (in_va_size sv_input) with Sv48.
  pose proof (entry_launch_ok_va_sp Sv48 rb_entry sv_input Hl Hok) as Hsp.
  pose proof (entry_launch_ok_va_base Sv48 rb_entry sv_input Hok) as Hmb.
  pose proof (entry_launch_ok_va_fits Sv48 rb_entry sv_input Hl Hok) as Hfit.
  unfold rb_entry in *. cbn [valid_entry_va].
  split; [exact Hsp | split; [| split; [exact Hmb | split; [exact Hfit | exact Hok]]]].
  unfold valid_brk. rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  repeat split; try lia; vm_compute; try reflexivity; try discriminate.
Qed.

Definition rb_start : Model := start_of rb_entry.

Definition rb_hint : Z := (va_stack_top Sv48 - 4096)%Z.

Example rb_hint_above_stack_honoured :
  summarize (mmap_at rb_hint)
    (check_syscall_for_run (mmap_in rb_hint f_hint) (mmap_at rb_hint) rb_start)
  = OOk rb_hint [(rb_hint, 4096%Z)].
Proof. vm_compute. reflexivity. Qed.
