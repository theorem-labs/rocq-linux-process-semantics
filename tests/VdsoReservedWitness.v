(* Written by the OSS-Fuzz proof collaborators. *)
(** * VdsoReservedWitness — the ASan plan checker stays off the launch's
      extra reserved intervals.

    [AsanPlanSound.cs_ok]'s [co_res] used to read
    [vm_reserved (m_vmmaps model) = segments_reserved SEGS], which asserted
    that the reserved ledger holds nothing but the image's own reservations.
    [State.init_model] also seeds it with what the kernel reserves for the
    process: the vvar pages and the vDSO text, taken as one unhinted
    [get_unmapped_area] span (Linux v6.18.46, commit 1f99e9ab748f,
    arch/riscv/kernel/vdso.c:124 [arch_setup_additional_pages]) that a
    top-down layout answers from the gap just below [mm->mmap_base].

    Two consumers concluded from [img_hi A <= lo] alone that a region above
    the image hull meets no reserved interval, and the pair sits exactly
    there.  This file is the evidence for the three parts of the repair:

    - [defect_region_above_the_hull_is_not_free]: the OLD conclusion is
      FALSE.  A region above [img_hi] meets the pair.
    - [node_refuses_past_the_floor] / [node_admits_below_the_floor]: the
      FIXED-over-free node refuses a request its ceiling
      ([AP.resx_clear] = [Z.min KHI (a_ylo cs)]) cannot place below the
      extra reservations, and still admits the neighbouring request one page
      clear of it.
    - [resx_free_below_the_floor] / [resx_met_above_the_floor]: on a
      concrete NON-EMPTY extra-reservation list, the floor is exactly what
      separates the two.

    WHY THE REFUSED REQUEST HERE IS NOT ITSELF OVER THE vDSO.  Every extra
    reservation clears [kHighMemBeg] ([APS.resx_entry_ok]), and the free
    path's ceiling is at or below [kHighMemBeg], so no request this node
    would otherwise admit can reach the pair.  That is a consequence of the
    repair, not a reason to leave the test out: the soundness proof
    ([AsanNodesMmLib.reserved_free_above]) is keyed to [a_ylo cs], the floor
    that tracks where the launch actually put its reservations, and the node
    test is keyed to the same thing.  A test keyed to the constant instead
    would go quiet the moment the ledger, the placement invariant or the
    launch's layout moved.  The pair below therefore uses a state whose
    [a_ylo] is the binding half of the ceiling, so that the half about the
    extra reservations is the one deciding the verdict. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Common Require Import AxSymExec3 AsanPlan AsanPlanSound.
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AP.

(** A launch that reserves ONE extra interval of twenty pages.  The image
    numbers are [AP.ASAN]'s; only [n_resx] and [p_resx] differ, and they are
    what a launch with the vDSO pair carries. *)
Definition AX : atable :=
  {| img_lo := 0x10000; img_hi := 0x671000; n_res := 4; n_resx := 1; p_resx := 20; shadow_off := 0x7fff8000;
     a_entry := 0x4ba64; rw_lo := 0x142000; rw_len := 0x52f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0xe1ea4; x_imemcpy := 0xe1e28; x_memset := 0x116934; x_memcpy := 0x116530; x_memiszero := 0xe2508;
     x_istrncpy := 0xe23b8; x_sealed := 0x1205f; x_popfree := 0x52a70;
     x_sniff := 0x1414dc; sniff_tab := 0x24f40; sniff_cell := 0x14bf00;
     x_envscan := 0x10d5e4; x_envscan_k := 0x10d5f0; x_pnscan := 0x10d6a8; x_pnscan_k := 0x10d6b4;
     stops_more := [0x506e4; 0x51d08; 0xddd88; 0xee070; 0xee200] |}.

Definition LIMITX : Z := 2 ^ 40.

(** the extra reservation: twenty pages based at the lowest address a launch
    can put them, [MBASE_MIN - resx_bytes AX], which is the initial
    [a_ylo] of [init_acs_of AX] *)
Definition RXBASE : Z := MBASE_MIN - resx_bytes AX.
Definition RX : list (word * word) := [(Z_to_bv 64 RXBASE, Z_to_bv 64 (resx_bytes AX))].

(** every goal here is a closed arithmetic fact: [vm_compute] takes each to a
    comparison of constructors, so [reflexivity] or [discriminate] closes it.
    [lia] does NOT: after [vm_compute] a [<=] has become [Gt = Gt -> False],
    which it cannot read. *)
Lemma RX_entry_ok : Forall (APS.resx_entry_ok AX) RX.
Proof.
  apply Forall_forall. intros iv Hin. cbn [In] in Hin. destruct Hin as [<-|[]].
  unfold APS.resx_entry_ok. cbn [fst snd].
  repeat split; vm_compute; first [reflexivity | discriminate].
Qed.

Lemma RX_count_and_size :
  (length RX <= n_resx AX)%nat /\ APS.sum_sizes RX <= resx_bytes AX.
Proof.
  split; [cbn [length RX AX n_resx]; lia | vm_compute; discriminate].
Qed.

(* ######################################################################### *)
(** * 1. The defect: above the image hull is NOT free                         *)
(* ######################################################################### *)

(** The image of this launch contributes nothing to the reserved ledger
    ([segments_reserved [] = []]), so the ledger is [RX] alone.  A region
    above [img_hi AX] — the only premise the two [reserved_free_above]
    copies used to take — meets it. *)
Example defect_region_above_the_hull_is_not_free :
  img_hi AX <= RXBASE
  /\ region_free (segments_reserved [] ++ RX) (Z_to_bv 64 RXBASE) (Z_to_bv 64 4096) = false.
Proof. split; vm_compute; [discriminate | reflexivity]. Qed.

(** and the floor is what separates free from met *)
Example resx_free_below_the_floor :
  region_free (segments_reserved [] ++ RX) (Z_to_bv 64 (RXBASE - 8192)) (Z_to_bv 64 4096) = true.
Proof. vm_compute. reflexivity. Qed.

Example resx_met_above_the_floor :
  region_free (segments_reserved [] ++ RX) (Z_to_bv 64 (RXBASE - 4096)) (Z_to_bv 64 8192) = false.
Proof. vm_compute. reflexivity. Qed.

(* ######################################################################### *)
(** * 2. The node: refuses past the floor, still admits below it              *)
(* ######################################################################### *)

(** a checker state with the two mmap registers set and a chosen [a_ylo].
    [a_ylo] descends by [2 * nhi] at every NULL-hint grant, so a plan drives
    it down; here it is set directly. *)
Definition with_ylo (cs : acs) (y : Z) : acs :=
  ACS (a_ss cs) (a_maps cs) (a_totsz cs) y (a_eager cs) (a_vis cs)
      (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

Definition YLO : Z := KHI - 3 * 4096.

Definition csX (addr len : Z) : acs :=
  with_ylo (set_reg (set_reg (init_acs_of AX) 10 (ELit addr)) 11 (ELit len)) YLO.

(** REFUSED: the request ends one page ABOVE the floor, so the checker cannot
    place it below the launch's extra reservations.  An undecided case
    refuses: the node returns [None] rather than granting. *)
Example node_refuses_past_the_floor :
  mmap_fixed_free AX LIMITX (csX (YLO - 4096) 8192) KRW false false = None.
Proof. vm_compute. reflexivity. Qed.

(** ADMITTED: the same request one page lower ends AT the floor, so it is
    provably clear of them, and the node still grants.  Without this half the
    pair would not show the checker still works. *)
Example node_admits_below_the_floor :
  exists cs', mmap_fixed_free AX LIMITX (csX (YLO - 8192) 4096) KRW false false = Some cs'.
Proof. eexists. vm_compute. reflexivity. Qed.

(** what the two requests differ in, stated as the test itself *)
Example the_floor_is_what_decides :
  resx_clear (csX (YLO - 4096) 8192) = YLO
  /\ (YLO - 4096) + 8192 > resx_clear (csX (YLO - 4096) 8192)
  /\ (YLO - 8192) + 4096 <= resx_clear (csX (YLO - 8192) 4096).
Proof. repeat split; vm_compute; first [reflexivity | discriminate]. Qed.
