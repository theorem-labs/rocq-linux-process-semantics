(** * LinuxProcessSem.Checks.Cases.Mm.Mremap — worked examples over mremap (216)

    Mirrors [Sys/Mm/Mremap.v], which answers to Linux [mm/mremap.c]:
    this file holds the worked examples for the syscalls defined there,
    and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude Fs.ReadWrite Mm.Mmap.

Definition mremap_two_page_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192)
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof)).

Definition mremap_in (old_size new_size : word) : SyscallInput :=
  (* a4 is deliberately nonzero: Linux ignores new_address without FIXED. *)
  mkInput 216 [65536; old_size; new_size; 1; 0x12345000; 0]
    (fun _ => None) (fun _ => None).

Example mremap_enomem_preserves_state :
  check_syscall (mremap_in 8192 4096)
    (mkEffect (errno_ret ENOMEM) [] []) mremap_two_page_model
  = CheckOk mremap_two_page_model [].
Proof. check_eq. Qed.

Definition mremap_shrunk_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 8192)
    mremap_two_page_model.

Example mremap_shrink_refunds_tail :
  check_syscall (mremap_in 8192 4096)
    (mkEffectU 65536 [] [] [(69632, 4096)] [] []) mremap_two_page_model
  = CheckOk mremap_shrunk_model [].
Proof. check_eq. Qed.

Example mremap_refund_is_regrantable :
  check_syscall
    (mkInput 222 [0; 4096; 3; 34; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 131072 [] [(131072, 4096)]) mremap_shrunk_model
  = CheckOk
      (with_vmmaps
        (mkVmMaps [] [(131072, 4096); (65536, 4096)] 0 0 8192)
        mremap_shrunk_model) [].
Proof. check_eq. Qed.

Definition mremap_budget_full_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 4096)
    (init_model [] 0 0 demo_sp 4096 (demo_input [] IEof)).

Example mremap_grow_beyond_budget_rejected :
  check_syscall (mremap_in 4096 8192)
    (mkEffect 65536 [] [(69632, 4096)]) mremap_budget_full_model
  = CheckReject.
Proof. check_eq. Qed.

Definition mremap_occupied_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096); (131072, 8192)] 0 0 16384)
    (init_model [] 0 0 demo_sp 16384 (demo_input [] IEof)).

Example mremap_move_to_occupied_range_rejected :
  check_syscall (mremap_in 4096 8192)
    (mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
      [mkCopy 65536 131072 4096] []) mremap_occupied_model
  = CheckReject.
Proof. check_eq. Qed.

Definition mremap_snapshot_mem (a : word) : option byte :=
  if bv_eqb a 65536 then Some 90
  else if bv_eqb a 65537 then Some 165
  else if bv_eqb a 196608 then Some 51
  else None.

Definition mremap_snapshot_ms : machine_state := {|
  ms_regs := bvmap_empty; ms_fregs := bvmap_empty; ms_pc_val := 0;
  ms_svc_pending := None; ms_resv := None; ms_fcsr := 0;
  ms_mem := mremap_snapshot_mem; ms_rom := fun _ => None
|}.

Definition mremap_snapshot_effect : SyscallEffect :=
  mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
    [mkCopy 65536 131072 4096] [].

Example mremap_copy_reads_pre_effect_snapshot :
  let after := ms_mem (apply_effect mremap_snapshot_ms mremap_snapshot_effect) in
  after 131072 = Some 90 /\
  after 131073 = Some 165 /\
  after 65536 = None /\
  after 135168 = Some 0 /\
  after 196608 = Some 51.
Proof. cbv zeta. repeat split; check_eq. Qed.

Example mremap_equal_size_accepts :
  check_syscall (mremap_in 8192 8192)
    (mkEffect 65536 [] []) mremap_two_page_model
  = CheckOk mremap_two_page_model [].
Proof. check_eq. Qed.

Example mremap_equal_size_enomem_rejected :
  check_syscall (mremap_in 8192 8192)
    (mkEffect (errno_ret ENOMEM) [] []) mremap_two_page_model
  = CheckReject.
Proof. check_eq. Qed.

Definition mremap_one_page_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 8192)
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof)).

Example mremap_inplace_grow_accepts :
  check_syscall (mremap_in 4096 8192)
    (mkEffectU 65536 [] [(69632, 4096)] [] [] []) mremap_one_page_model
  = CheckOk
      (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192)
         mremap_one_page_model) [].
Proof. check_eq. Qed.

Definition mremap_crowded_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096); (69632, 4096)] 0 0 16384)
    (init_model [] 0 0 demo_sp 16384 (demo_input [] IEof)).

Example mremap_inplace_grow_into_neighbour_rejected :
  check_syscall (mremap_in 4096 8192)
    (mkEffectU 65536 [] [(69632, 4096)] [] [] []) mremap_crowded_model
  = CheckReject.
Proof. check_eq. Qed.

Definition mremap_below_image_model : Model :=
  with_vmmaps (mkVmMaps [(69632, 4096)] [(65536, 4096)] 0 0 8192)
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof)).

Example mremap_inplace_grow_into_image_rejected :
  check_syscall (mremap_in 4096 8192)
    (mkEffectU 65536 [] [(69632, 4096)] [] [] []) mremap_below_image_model
  = CheckReject.
Proof. check_eq. Qed.

Example mremap_move_out_of_the_image_accepts :
  check_syscall (mremap_in 4096 8192)
    (mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
      [mkCopy 65536 131072 4096] []) mremap_below_image_model
  = CheckOk
      (with_vmmaps (mkVmMaps [(69632, 4096)] [(131072, 8192)] 0 0 8192)
         mremap_below_image_model) [].
Proof. check_eq. Qed.

Definition mremap_at_in (old_addr old_size new_size : word) : SyscallInput :=
  mkInput 216 [old_addr; old_size; new_size; 1; 0x12345000; 0]
    (fun _ => None) (fun _ => None).

Definition mremap_grow_to_ceiling_model : Model :=
  with_vmmaps (mkVmMaps [] [(140735332474880, 4096)] 0 0 8192)
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof)).

Example mremap_inplace_grow_to_ceiling_accepts :
  check_syscall (mremap_at_in 140735332474880 4096 8192)
    (mkEffectU 140735332474880 [] [(140735332478976, 4096)] [] [] [])
    mremap_grow_to_ceiling_model
  = CheckOk
      (with_vmmaps (mkVmMaps [] [(140735332474880, 8192)] 0 0 8192)
         mremap_grow_to_ceiling_model) [].
Proof. check_eq. Qed.

Definition mremap_grow_past_ceiling_model : Model :=
  with_vmmaps (mkVmMaps [] [(140735332478976, 4096)] 0 0 8192)
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof)).

Example mremap_inplace_grow_past_ceiling_rejected :
  check_syscall (mremap_at_in 140735332478976 4096 8192)
    (mkEffectU 140735332478976 [] [(140735332483072, 4096)] [] [] [])
    mremap_grow_past_ceiling_model
  = CheckReject.
Proof. check_eq. Qed.

Example mremap_move_down_from_ceiling_accepts :
  check_syscall (mremap_at_in 140735332478976 4096 8192)
    (mkEffectU 65536 [] [(69632, 4096)] [(140735332478976, 4096)]
      [mkCopy 140735332478976 65536 4096] []) mremap_grow_past_ceiling_model
  = CheckOk
      (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192)
         mremap_grow_past_ceiling_model) [].
Proof. check_eq. Qed.

Example mremap_wrapping_new_size_is_einval :
  check_syscall (mremap_in 8192 18446744073709551615)
    (mkEffect (errno_ret EINVAL) [] []) mremap_two_page_model
  = CheckOk mremap_two_page_model [].
Proof. check_eq. Qed.

Example mremap_wrapping_new_size_success_rejected :
  check_syscall (mremap_in 8192 18446744073709551615)
    (mkEffect 65536 [] []) mremap_two_page_model
  = CheckReject.
Proof. check_eq. Qed.

(** A NEW SIZE AT THE TOP OF THE ADDRESS SPACE is -EINVAL, not the
    arm's injected -ENOMEM.  It is page aligned, so it passes the
    wrap gate above, and [check_mremap_params] then refuses it for
    exceeding TASK_SIZE (mm/mremap.c:1775-1776, Linux v6.18.46),
    before any VMA is looked up.  These two examples pinned -ENOMEM
    until that gate was added; they pinned an answer Linux never
    gives. *)
Example mremap_top_aligned_new_size_is_einval :
  check_syscall (mremap_in 8192 18446744073709547520)
    (mkEffect (errno_ret EINVAL) [] []) mremap_two_page_model
  = CheckOk mremap_two_page_model [].
Proof. check_eq. Qed.

Example mremap_top_aligned_new_size_enomem_rejected :
  check_syscall (mremap_in 8192 18446744073709547520)
    (mkEffect (errno_ret ENOMEM) [] []) mremap_two_page_model
  = CheckReject.
Proof. check_eq. Qed.

Definition mremap_misaligned_in (old_size new_size : word) : SyscallInput :=
  mkInput 216 [65537; old_size; new_size; 1; 0x12345000; 0]
    (fun _ => None) (fun _ => None).

Example mremap_old_size_zero_after_einval_gates :
  check_syscall (mremap_misaligned_in 0 4096)
    (mkEffect (errno_ret EINVAL) [] []) mremap_two_page_model
  = CheckOk mremap_two_page_model [].
Proof. check_eq. Qed.

Example mremap_old_size_zero_aligned_is_unmodeled :
  check_syscall (mremap_in 0 4096)
    (mkEffect (errno_ret EINVAL) [] []) mremap_two_page_model
  = CheckUnmodeled.
Proof. check_eq. Qed.

Definition mremap_zero_entry_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 0)] 0 0 8192)
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof)).

Example mremap_zero_entry_passes_the_source_gate :
  mremap_source_b (m_vmmaps mremap_zero_entry_model) 65536 0 0 = true.
Proof. check_eq. Qed.

Example mremap_old_size_zero_gate_precedes_the_source_gate :
  check_syscall (mremap_in 0 4096)
    (mkEffect (errno_ret ENOMEM) [] []) mremap_zero_entry_model
  = CheckUnmodeled.
Proof. check_eq. Qed.

Lemma mremap_wrapping_old_size_cannot_pass_the_source_gate :
  forall h old old_n old_nZ,
    (two_pow_64 <= old_nZ)%Z ->
    mremap_source_b h old old_n old_nZ = false.
Proof.
  intros h old old_n old_nZ Hwrap. unfold mremap_source_b.
  pose proof (word_unsigned_range old) as Hold.
  replace ((bv_unsigned old + old_nZ <=? alloc_top h)%Z) with false.
  - reflexivity.
  - symmetry. apply Z.leb_gt.
    alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

Example mremap_wrapping_old_size_rounds_past_the_word :
  (two_pow_64 <=? page_round_up_Z (bv_unsigned (18446744073709551615 : word)))%Z
  = true.
Proof. vm_compute. reflexivity. Qed.

Example mremap_wrapping_old_size_is_unmodeled :
  check_syscall (mremap_in 18446744073709551615 4096)
    (mkEffect (errno_ret ENOMEM) [] []) mremap_two_page_model
  = CheckUnmodeled.
Proof. check_eq. Qed.

Lemma mremap_move_gap_is_the_retained_source :
  forall h old dst old_n new_n,
    bv_eqb dst old = false ->
    map_has (vm_maps (mremap_maps_next h old dst new_n)) old old_n = false
    /\ forall r n,
         region_free
           ((old, old_n) :: vm_reserved h
              ++ vm_maps (mremap_maps_next h old dst new_n)) r n = true
         <->
         iv_overlap r n old old_n = false
         /\ region_free
              (vm_reserved h
                 ++ vm_maps (mremap_maps_next h old dst new_n)) r n = true.
Proof.
  intros h old dst old_n new_n Hdst. split.
  - unfold mremap_maps_next, map_has, map_remove. cbn [vm_maps existsb fst].
    rewrite Hdst. cbn [andb orb].
    apply not_true_is_false. rewrite existsb_exists.
    intros [p [Hin Hp]]. apply filter_In in Hin. destruct Hin as [_ Hne].
    apply andb_true_iff in Hp. destruct Hp as [Hfst _].
    rewrite Hfst in Hne. discriminate.
  - intros r n. cbn [region_free]. split.
    + intros H. apply andb_true_iff in H. destruct H as [H1 H2].
      split; [apply negb_true_iff in H1; exact H1 | exact H2].
    + intros [H1 H2]. apply andb_true_iff.
      split; [apply negb_true_iff; exact H1 | exact H2].
Qed.

Example apply_effect_zeros_run_after_unmaps :
  ms_mem (apply_effect mremap_snapshot_ms
            (mkEffectU 0 [] [(65536, 4096)] [(65536, 4096)] [] [])) 65536
  = Some 0.
Proof. check_eq. Qed.

Example apply_effect_copies_run_after_zeros :
  ms_mem (apply_effect mremap_snapshot_ms
            (mkEffectU 0 [] [(131072, 4096)] []
               [mkCopy 65536 131072 4096] [])) 131072
  = Some 90.
Proof. check_eq. Qed.

Example apply_effect_writes_run_after_copies :
  ms_mem (apply_effect mremap_snapshot_ms
            (mkEffectU 0 [(131072, [7])] [] []
               [mkCopy 65536 131072 4096] [])) 131072
  = Some 7.
Proof. check_eq. Qed.

Example apply_effect_copy_source_survives_unmap_and_zero :
  let after := ms_mem (apply_effect mremap_snapshot_ms
                 (mkEffectU 0 [] [(65536, 4096)] [(65536, 4096)]
                    [mkCopy 65536 131072 4096] [])) in
  after 131072 = Some 90 /\ after 65536 = Some 0.
Proof. cbv zeta. repeat split; check_eq. Qed.

Definition mremap_orphan_in : SyscallInput :=
  (* a4 is deliberately nonzero: Linux ignores new_address without FIXED. *)
  mkInput 216 [131072; 4096; 8192; 1; 0x12345000; 0]
    (fun _ => None) (fun _ => None).

Example mremap_move_onto_brk_orphan_page_rejected :
  check_syscall mremap_orphan_in
    (mkEffectU 65536 [] [(69632, 4096)] [(131072, 4096)]
      [mkCopy 131072 65536 4096] []) m_brk_orphan_with_source
  = CheckReject.
Proof. check_eq. Qed.

Example mremap_move_above_brk_orphan_accepts :
  check_syscall mremap_orphan_in
    (mkEffectU 69632 [] [(73728, 4096)] [(131072, 4096)]
      [mkCopy 131072 69632 4096] []) m_brk_orphan_with_source
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull brk_reserved [(69632, 8192); (65536, 4084)]
          [(65536, 4096)] 65536 69620 demo_limit 0 demo_sp)
        m_brk_orphan_with_source) [].
Proof. check_eq. Qed.

Example mremap_move_onto_orphan_without_residual_accepts :
  check_syscall mremap_orphan_in
    (mkEffectU 65536 [] [(69632, 4096)] [(131072, 4096)]
      [mkCopy 131072 65536 4096] []) m_brk_orphan_without_residual
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull brk_reserved [(65536, 8192)]
          [(65536, 4096)] 65536 69620 demo_limit 0 demo_sp)
        m_brk_orphan_without_residual) [].
Proof. check_eq. Qed.

Definition mremap_lazy_two_pages : Model :=
  with_vm_backing [(65536, 8192)] [65536; 69632]
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192)
      (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof))).

Example mremap_lazy_shrink_drops_tail_charge :
  check_syscall (mremap_in 8192 4096)
    (mkEffectU 65536 [] [] [(69632, 4096)] [] []) mremap_lazy_two_pages
  = CheckOk
      (mremap_model_next mremap_lazy_two_pages 65536 8192 65536 4096) [].
Proof. check_eq. Qed.

Example mremap_lazy_shrink_ledgers_are_exact :
  let post := mremap_model_next mremap_lazy_two_pages
                65536 8192 65536 4096 in
  m_vm_lazy post = [(65536, 4096)] /\
  m_vm_materialized post = [65536] /\
  vm_backing_used post = 4096%Z.
Proof. cbv zeta. repeat split; check_eq. Qed.

Definition mremap_lazy_one_page : Model :=
  with_vm_backing [(65536, 4096)] [65536]
    (with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 4096)
      (init_model [] 0 0 demo_sp 4096 (demo_input [] IEof))).

(** A lazy grow succeeds at a full backed budget because its new tail is a
    reservation, not an eager charge. *)
Example mremap_lazy_grow_bypasses_eager_delta :
  check_syscall (mremap_in 4096 8192)
    (mkEffectU 65536 [] [(69632, 4096)] [] [] []) mremap_lazy_one_page
  = CheckOk
      (mremap_model_next mremap_lazy_one_page 65536 4096 65536 8192) [].
Proof. check_eq. Qed.

Example mremap_lazy_grow_preserves_only_old_charge :
  let post := mremap_model_next mremap_lazy_one_page
                65536 4096 65536 8192 in
  m_vm_lazy post = [(65536, 8192)] /\
  m_vm_materialized post = [65536] /\
  vm_backing_used post = 4096%Z.
Proof. cbv zeta. repeat split; check_eq. Qed.

Example mremap_lazy_move_relocates_materialized_pages :
  check_syscall (mremap_in 4096 8192)
    (mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
      [mkCopy 65536 131072 4096] []) mremap_lazy_one_page
  = CheckOk
      (mremap_model_next mremap_lazy_one_page 65536 4096 131072 8192) [].
Proof. check_eq. Qed.

Example mremap_lazy_move_ledgers_follow_contents :
  let post := mremap_model_next mremap_lazy_one_page
                65536 4096 131072 8192 in
  m_vm_lazy post = [(131072, 8192)] /\
  m_vm_materialized post = [131072] /\
  vm_backing_used post = 4096%Z.
Proof. cbv zeta. repeat split; check_eq. Qed.

Definition mremap_mixed_backing : Model :=
  with_vm_backing [(65536, 4096)] []
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192)
      (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof))).

Example mremap_mixed_backing_fails_closed :
  check_syscall (mremap_in 8192 4096)
    (mkEffectU 65536 [] [] [(69632, 4096)] [] []) mremap_mixed_backing
  = CheckUnmodeled.
Proof. check_eq. Qed.

(* -------------------------------------------------------------------------
   Moved destinations are preference-free placements

   Linux picks a MAYMOVE destination with [get_unmapped_area] at
   [addr = 0] (mm/mremap.c:1170, cited on [Mremap.mremap_fresh_b]), so
   whatever the spec is entitled to say about a preference-free mmap
   placement it is entitled to say here, and no more.  That is three
   conditions — page-aligned, inside the user range, disjoint from every
   recorded mapping — and these cases pin both halves of it on a move.

   The spec does not pin the search as well: that would exclude
   placements Linux makes (see the placement section in
   [Sys/Mm/Mmap.v]), so the low destination is admissible here for
   exactly the reason it is admissible for a fresh grant.

   Reason 4 for all of them: the kernel's allocator descends from an
   [mmap_base] no lower than [State.mmap_base_min] = 0x154555557000 under
   the configuration SCOPE.md names (mm/util.c [mmap_base], v6.18.46;
   [Checks.Cases.MmapBase.sv48_band_is_linux_set]) and never produces a
   destination this low, so only these cases can say what the spec does
   with one.
   ------------------------------------------------------------------------- *)

Definition mremap_placed_in (old_addr old_size new_size : word)
    : SyscallInput :=
  mkInput 216 [old_addr; old_size; new_size; 1; 0; 0]
    (fun _ => None) (fun _ => None).

Definition mremap_placement_model : Model :=
  with_vmmaps
    (mkVmMapsFull [] [(Z_to_bv 64 0x2aaaaab000, 4096)] [] 0 0 8192
      (Z_to_bv 64 mmap_base_max) demo_sp)
    (init_model [] 0 (Z_to_bv 64 mmap_base_max) demo_sp 8192 (demo_input [] IEof)).

(** A growing move to a low destination, admitted: 0x80000000 is
    page-aligned, positive, below the ceiling and free, which is
    everything the spec asks of a preference-free placement. *)
Example mremap_move_low_destination_admitted :
  check_syscall (mremap_placed_in (Z_to_bv 64 0x2aaaaab000) 4096 8192)
    (mkEffectU (Z_to_bv 64 0x80000000) []
       [(Z_to_bv 64 0x80001000, 4096)]
       [(Z_to_bv 64 0x2aaaaab000, 4096)]
       [mkCopy (Z_to_bv 64 0x2aaaaab000) (Z_to_bv 64 0x80000000) 4096] [])
    mremap_placement_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(Z_to_bv 64 0x80000000, 8192)] [] 0 0 8192
          (Z_to_bv 64 mmap_base_max) demo_sp) mremap_placement_model) [].
Proof. check_eq. Qed.

(** NEGATIVE: the conditions that DO refuse a move still refuse it.  An
    unaligned destination is rejected… *)
Example mremap_move_unaligned_destination_rejected :
  check_syscall (mremap_placed_in (Z_to_bv 64 0x2aaaaab000) 4096 8192)
    (mkEffectU (Z_to_bv 64 0x80000001) []
       [(Z_to_bv 64 0x80001001, 4096)]
       [(Z_to_bv 64 0x2aaaaab000, 4096)]
       [mkCopy (Z_to_bv 64 0x2aaaaab000) (Z_to_bv 64 0x80000001) 4096] [])
    mremap_placement_model
  = CheckReject.
Proof. check_eq. Qed.

(** …and so is one that OVERLAPS the source, which is the disjointness
    condition doing the work a move most needs it for: Linux runs the
    destination search while the source VMA is still live (it is not
    unmapped until [move_vma] reaches [unmap_source_vma], mm/mremap.c,
    Linux v6.18.46 — the search is over before any of it runs), so the
    destination cannot be a range the source still holds, and the model
    gets that exclusion from [old] still being in [vm_maps] when
    [region_free] runs.

    THE ADDRESS IS CHOSEN SO THAT ONLY [region_free] REFUSES IT.  The
    destination starts one page BELOW the source and is two pages long,
    so it covers the source's page without starting on it: [dst <> old]
    holds, the alignment, positivity and ceiling conjuncts hold, and the
    budget holds.  Landing exactly ON the source would not test this —
    [mremap_fresh_b]'s first conjunct is [negb (bv_eqb dst old)], which
    refuses [dst = old] before [region_free] is ever consulted, so such
    a case stays [CheckReject] with the disjointness conjunct deleted
    and pins nothing.  This one does not: deleting [region_free] from
    [mremap_fresh_b] turns it into a [CheckOk]. *)

(** The source and the overlapping destination are NAMED, and the case
    below and its witness both use the names.  Spelling the addresses
    twice would let the witness drift off the case it is evidence for —
    an edit to one set of literals leaves the other proving something
    true about an address nobody tests — and a witness that can drift is
    a witness nobody should trust. *)
Definition mremap_src : word := Z_to_bv 64 0x2aaaaab000.
Definition mremap_src_n : word := Z_to_bv 64 4096.
Definition mremap_overlapping_dst : word := Z_to_bv 64 0x2aaaaaa000.
Definition mremap_overlapping_dst_n : word := Z_to_bv 64 8192.

Example mremap_move_onto_source_rejected :
  check_syscall (mremap_placed_in mremap_src 4096 8192)
    (mkEffectU mremap_overlapping_dst []
       [(mremap_src, 4096)]
       [(mremap_src, 4096)]
       [mkCopy mremap_src mremap_overlapping_dst 4096] [])
    mremap_placement_model
  = CheckReject.
Proof. check_eq. Qed.

(** …and the uniqueness is CHECKED rather than asserted, since a
    negative that fails for the wrong reason pins nothing.  At this
    destination every other conjunct of [Mremap.mremap_fresh_b] holds
    and only [region_free] fails; at [dst = old] the FIRST conjunct
    fails and [region_free] is never reached, which is why that
    spelling would have been vacuous.

    Each conjunct below is the guard's, at the same arguments the case
    above passes: [mremap_overlapping_dst] for [dst],
    [mremap_overlapping_dst_n] for [new_n], [mremap_src] for [old].  That
    the six are ALL of them is pinned separately, by
    [mremap_fresh_b_conjuncts] below. *)
Example mremap_move_onto_source_only_region_free_fails :
  region_free (vm_reserved (m_vmmaps mremap_placement_model)
               ++ vm_maps (m_vmmaps mremap_placement_model))
    mremap_overlapping_dst mremap_overlapping_dst_n = false
  /\ negb (bv_eqb mremap_overlapping_dst mremap_src) = true
  /\ (bv_unsigned mremap_overlapping_dst mod page_size =? 0)%Z = true
  /\ (0 <? bv_unsigned mremap_overlapping_dst)%Z = true
  /\ (bv_unsigned mremap_overlapping_dst
       + bv_unsigned mremap_overlapping_dst_n
         <=? alloc_top (m_vmmaps mremap_placement_model))%Z = true
  /\ mremap_final_budget_b mremap_placement_model
       mremap_src mremap_src_n
       mremap_overlapping_dst mremap_overlapping_dst_n = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** …and the spelling that would NOT have bitten, recorded so the choice
    above reads as forced rather than arbitrary: at [dst = old] the
    guard's first conjunct is already false.  This one is documentary
    rather than a test — it is [reflexivity] on a ground term — and is
    kept for what it explains, not for what it checks. *)
Example mremap_move_dst_eq_old_is_refused_before_region_free :
  negb (bv_eqb mremap_src mremap_src) = false.
Proof. reflexivity. Qed.

(** THE ENUMERATION IS PINNED BY THE BUILD, which is the other half of
    making that witness trustworthy.  It lists the guard's conjuncts,
    but nothing in it says the list is COMPLETE: add a seventh conjunct
    to [Mremap.mremap_fresh_b] and the witness keeps passing while
    quietly ceasing to be the uniqueness argument its name claims.  This
    states the guard's shape, so that edit breaks the build instead.

    STATED AT ABSTRACT ARGUMENTS ON PURPOSE.  At the concrete ones the
    case uses, [vm_compute] reduces BOTH sides to [false] and the
    equation holds for reasons having nothing to do with the shape —
    which is precisely the vacuity these cases guard against, and
    would have hidden a seventh conjunct rather than exposing it.
    Quantified, neither side computes and [reflexivity] is the
    definitional unfolding. *)
Lemma mremap_fresh_b_conjuncts :
  forall m old_nZ new_nZ old old_n dst new_n,
    mremap_fresh_b m old_nZ new_nZ old old_n dst new_n
    = (negb (bv_eqb dst old)
       && (bv_unsigned dst mod page_size =? 0)%Z
       && (0 <? bv_unsigned dst)%Z
       && (bv_unsigned dst + new_nZ <=? alloc_top (m_vmmaps m))%Z
       && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
            dst new_n
       && mremap_final_budget_b m old old_n dst new_n).
Proof. reflexivity. Qed.

(** …and the ordinary move, one page above the source, is admitted. *)
Example mremap_move_just_above_source_accepts :
  check_syscall (mremap_placed_in (Z_to_bv 64 0x2aaaaab000) 4096 8192)
    (mkEffectU (Z_to_bv 64 0x2aaaaac000) []
       [(Z_to_bv 64 0x2aaaaad000, 4096)]
       [(Z_to_bv 64 0x2aaaaab000, 4096)]
       [mkCopy (Z_to_bv 64 0x2aaaaab000) (Z_to_bv 64 0x2aaaaac000) 4096] [])
    mremap_placement_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(Z_to_bv 64 0x2aaaaac000, 8192)] [] 0 0 8192
          (Z_to_bv 64 mmap_base_max) demo_sp) mremap_placement_model) [].
Proof. check_eq. Qed.


(* -------------------------------------------------------------------------
   THE BOUND IS READ FROM THE LEDGER, for mremap's two placing arms.  The
   same two effects [mremap_inplace_grow_past_ceiling_rejected] and the
   moved-destination case refuse under [demo_sp] are admitted once the
   ledger's stack pointer is [hi_sp] (see the twin block at the end of
   [Cases/Mm/Mmap.v] for the argument).
   ------------------------------------------------------------------------- *)

Definition mremap_grow_past_top_hi_model : Model :=
  with_vmmaps
    (mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096)] [] 0 0 8192
      (Z_to_bv 64 mmap_base_max) hi_sp)
    (init_model [] 0 (Z_to_bv 64 mmap_base_max) hi_sp 8192 (demo_input [] IEof)).

Example mremap_inplace_grow_past_demo_top_admitted_under_high_sp :
  check_syscall (mremap_at_in (Z_to_bv 64 (demo_top - 4096)) 4096 8192)
    (mkEffectU (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 demo_top, 4096)] [] [] [])
    mremap_grow_past_top_hi_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 8192)] [] 0 0 8192
          (Z_to_bv 64 mmap_base_max) hi_sp) mremap_grow_past_top_hi_model) [].
Proof. check_eq. Qed.

Definition mremap_move_source_lo_model : Model :=
  with_vmmaps
    (mkVmMapsFull [] [(65536, 4096)] [] 0 0 8192
      (Z_to_bv 64 mmap_base_max) demo_sp)
    (init_model [] 0 (Z_to_bv 64 mmap_base_max) demo_sp 8192 (demo_input [] IEof)).
Definition mremap_move_source_hi_model : Model :=
  with_vmmaps
    (mkVmMapsFull [] [(65536, 4096)] [] 0 0 8192
      (Z_to_bv 64 mmap_base_max) hi_sp)
    (init_model [] 0 (Z_to_bv 64 mmap_base_max) hi_sp 8192 (demo_input [] IEof)).

(** A move whose destination ends one page past [demo_top]. *)
Example mremap_move_past_demo_top_rejected_under_low_sp :
  check_syscall (mremap_at_in 65536 4096 8192)
    (mkEffectU (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 demo_top, 4096)]
       [(65536, 4096)] [mkCopy 65536 (Z_to_bv 64 (demo_top - 4096)) 4096] [])
    mremap_move_source_lo_model
  = CheckReject.
Proof. check_eq. Qed.

Example mremap_move_past_demo_top_admitted_under_high_sp :
  check_syscall (mremap_at_in 65536 4096 8192)
    (mkEffectU (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 demo_top, 4096)]
       [(65536, 4096)] [mkCopy 65536 (Z_to_bv 64 (demo_top - 4096)) 4096] [])
    mremap_move_source_hi_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 8192)] [] 0 0 8192
          (Z_to_bv 64 mmap_base_max) hi_sp) mremap_move_source_hi_model) [].
Proof. check_eq. Qed.

(** A NEW LENGTH OVER [State.TASK_SIZE] is -EINVAL, and the answer is
    deterministic: [check_mremap_params] (mm/mremap.c:1775-1776, Linux
    v6.18.46) rejects it before any VMA is looked up.  The first three
    conjuncts use an [old_size] the model's ledger does NOT hold exactly,
    so before this gate the answer was [Unmodeled]: they pin that the gate
    fires AHEAD of the source test, which is the kernel's order
    ([do_mremap] calls [check_mremap_params] at :1920-1922 and
    [vma_lookup] only at :1931).  The fourth and fifth use the source the
    ledger does hold, where the answer before this gate was the arm's
    injected -ENOMEM, the answer Linux never gives here. *)
Example mremap_new_len_over_task_size_is_einval :
  check_syscall (mremap_in 4096 (Z_to_bv 64 (TASK_SIZE + 1)))
    (mkEffect (errno_ret EINVAL) [] []) mremap_two_page_model
  = CheckOk mremap_two_page_model []
  /\ check_syscall (mremap_in 4096 (Z_to_bv 64 (TASK_SIZE + 1)))
       (mkEffect (errno_ret ENOMEM) [] []) mremap_two_page_model
     = CheckReject
  /\ check_syscall (mremap_in 4096 (Z_to_bv 64 (TASK_SIZE + 1)))
       (mkEffect 65536 [] []) mremap_two_page_model
     = CheckReject
  /\ check_syscall (mremap_in 8192 (Z_to_bv 64 (TASK_SIZE + 1)))
       (mkEffect (errno_ret EINVAL) [] []) mremap_two_page_model
     = CheckOk mremap_two_page_model []
  /\ check_syscall (mremap_in 8192 (Z_to_bv 64 (TASK_SIZE + 1)))
       (mkEffect (errno_ret ENOMEM) [] []) mremap_two_page_model
     = CheckReject
  (* ...while a new length of exactly TASK_SIZE passes the gate and
     reaches the grow arm, whose injected -ENOMEM is admitted *)
  /\ check_syscall (mremap_in 8192 (Z_to_bv 64 TASK_SIZE))
       (mkEffect (errno_ret ENOMEM) [] []) mremap_two_page_model
     = CheckOk mremap_two_page_model []
  /\ check_syscall (mremap_in 8192 (Z_to_bv 64 TASK_SIZE))
       (mkEffect (errno_ret EINVAL) [] []) mremap_two_page_model
     = CheckReject.
Proof. repeat split; first [ check_eq | vm_compute; reflexivity ]. Qed.
