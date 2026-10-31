(* Written by the OSS-Fuzz proof collaborators. *)
(** * AsanNodesIface — what helper "nodes" proves (files AsanNodesMm*.v)

    The plan checker [AsanPlan.AP.check] is proved sound
    ([AsanPlanSound.APS.check_sound], conclusion [SpinAlg.srealizes]) from
    per-node statements that are Section hypotheses of [APS].  This file
    CLOSES those statements over the Section parameters, under the standard
    parameter/hypothesis block every node package uses, and names one
    obligation per node.  An integration file instantiates them at the image
    and the start-up / main-phase invariants.

    PARAMETER BLOCK (open this Section verbatim in your files):
<<
Section Nodes.
Variable SEGS : list Segment.            Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.          (= length (segments_reserved SEGS) = n_res A)
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                             (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
>>
    (you may add the hypothesis [LIMIT = target_alloc_limit] if a budget
    argument needs the number; nothing else).

    OBLIGATIONS (Lemma names fixed; statements are the [OBL_*] below with the
    parameters of the block; all conclusions are [srealizes] — anything you
    prove with [ShapeAlg.realizes] lifts by [SpinAlg.srealizes_of_realizes];
    two/three-child conclusions [t_alt2 TA TB] / [t_alt2 TA (t_alt2 TB TC)]
    are assembled with [SpinAlg.srz_node]/[srz_alt2] over the index type of
    the spec's resolutions — see AsanNodesMmA.v / AsanNodesMmB.v for
    the cs_ok re-establishment per arm, and RefNodes.v / MmapSim.v /
    AllocSim.v / NoReserve.v for the spec's inversion lemmas):

    M1 [node_mmap2_sound   : OBL_mmap2]     [AP.node_mmap2 A nx0 LIMIT]   (checker: AsanPlanCore §8.3)
         child a = REFUSED ([APC.refuse]: a0 := 2^64-12, pc+4, model unchanged; spec arm
         [e <- errno_from [ENOMEM];; err_ret e]);
         child b = GRANTED: NULL hint ([APC.mmap_null]; arms P (3,0x22) / A (3,0x4022) / B0 (0,0x22) / B (0,0x4022);
         spec [mmap_modeled_b]/[mmap_noaccess_b] NULL-hint branches, [choose a. …]; the grant witness comes from
         [APC.gap_ok] via [AsanPlacement.free_gap_of_totals] + [co_totsz] + [RES_len], placement LOWER bound
         (new base > KHI) from [co_split] via [AsanPlacement.kHighMemBeg_le]/[null_hint_grant_step],
         budget (arm P only) from [APC.budget_ok] + [co_eager] + [co_abytes] + [co_minv])
         or FIXED over a FREE range ([APC.mmap_fixed_free]; arms C (3,0x4032) / C0 (3,0x32) / D (0,0x4032) / D0 (0,0x32);
         spec: the [region_free (vm_reserved h ++ vm_maps h) addr n] sub-branches with [choose a. a = addr /\ …]).
    M2 [node_mmapin_sound  : OBL_mmapin]    [AP.node_mmapin A LIMIT]
         MAP_FIXED wholly inside ONE tracked entry (spec: [region_free (vm_reserved h) addr n && map_contains (vm_maps h) addr n]
         branches of [mmap_fixed_noaccess_b] / [mmap_fixed_rw_b]): child a = REFUSED-kept ([APC.refuse]);
         child b = OK ([APC.mmap_fixed_in] arm E (3,0x32) / F (3,0x4032) / G (0,0x32 or 0,0x4032); post-model
         [with_mmap_replacement flags addr n (with_vmmaps …)]); child c = REFUSED-destroyed ([APC.mmap_destroyed]:
         [with_mmap_destroyed addr n h'] with both ledgers [maps_subtract]ed, effect unmaps [addr, addr+n)).
    M3 [node_mprotect2_sound : OBL_mprotect2] [AP.node_mprotect2 A LIMIT]
         child a = REFUSED; child b = [APC.node_mprotect] (Mprotect.v: [map_contains noaccess && map_contains maps] branch).
    M4 [node_brk2_sound    : OBL_brk2]      [AP.node_brk2 A LIMIT]   (Mmap.v [brk_r_ok] GROW:
         child a = stay (r = b), child b = grow (r = req, [brk_grow_ok])).
    M5 [node_sys_sound     : OBL_sys]       [AP.node_sys A nx0 y] for y ∈ {YBrk, YSetTid}
         (brk query / provably blocked grow — r = b only; set_tid_address).
    M5b [node_munmap2_sound : OBL_munmap2]  [APC.node_munmap2 A]   (Mmap.v [munmap_spec] EXACT arm:
         child a = REFUSED ([APC.refuse]: a0 := -ENOMEM, model unchanged — Linux reattaches the vmas
         when [vma_iter_clear_gfp] fails, mm/vma.c:1573/1581 at v6.18.46);
         child b = the cut of exactly one tracked entry).
    M6 [node_exit_sound    : OBL_exit]      [APC.node_exit]  (exit 93 / exit_group 94 → [t_exit]).
    The [PSpin] leaf, PRun, PX summaries, PFresh, PJoin and hooks are not node obligations. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section Iface.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

(** the statements, closed (these are what [APS.check_sound] consumes) *)
Definition OBL_mmap2 : Prop := mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mmap2 A nx0 LIMIT).
Definition OBL_mmapin : Prop := forall hole : bool, mm3_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mmapin A LIMIT hole).   (* hole = PMmapInH *)
Definition OBL_mprotect2 : Prop := mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mprotect2 A LIMIT).
Definition OBL_brk2 : Prop := brk2_stmt SEGS A nx0 LIMIT SINV argH FS0.
Definition OBL_munmap2 : Prop := munmap2_stmt SEGS A nx0 LIMIT SINV argH FS0.
Definition OBL_sys : Prop := forall y : snode, sys_stmt SEGS A nx0 LIMIT SINV argH FS0 y.
Definition OBL_exit : Prop := exit_stmt SEGS A LIMIT SINV argH FS0.

(** all of them (what an integration file assumes about one image / invariant) *)
Definition OBL_all : Prop := OBL_mmap2 /\ OBL_mmapin /\ OBL_mprotect2 /\ OBL_brk2 /\ OBL_munmap2 /\ OBL_sys /\ OBL_exit.

(** Unfolded reading of the two-child template, for reference (definitionally
    equal to [OBL_mmap2]; do not restate it differently). *)
Lemma OBL_mmap2_unfold :
  OBL_mmap2 <->
  forall cs csa csb E R FULL model TA TB,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model ->
    is_ecall_at SEGS cs = true ->
    node_mmap2 A nx0 LIMIT cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A LIMIT SINV argH FS0 E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg_of SEGS R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A LIMIT SINV argH FS0 E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg_of SEGS R' (pc csb) FULL' model') TB) ->
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) (t_alt2 TA TB).
Proof. unfold OBL_mmap2, mm2_stmt. tauto. Qed.
End Iface.
