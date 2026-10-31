(** * LinuxProcessSemantics.Common.WfInvariant -- the ledger invariant, proved

    [Sys/Mm/Mremap.v], above [mremap_move_charge], says of its lazy and
    materialized halves: "the ledger invariant the writers of [vm_lazy]
    keep -- every reservation lies under a live mapping -- which is not yet
    a proved invariant and is taken as a hypothesis where the lemma is
    used."  This file proves it, so that sentence can be withdrawn.

    [WF] is the invariant:

      WF m := NoaccessOwned.sys_inv (m_vmmaps m) /\ LZ_OWNED m /\ MAT_OWNED m

    established at [Run.init_config] and preserved by every writer of the
    ledgers.  OWNERSHIP IS OF THE PAGE FLOOR, NOT OF THE BYTE, and
    [MAT_OWNED]'s alignment conjunct is load-bearing.  Both are forced by
    the [brk] arm: [Mmap.brk_maps_next] cuts [[r, b)] out of every entry
    byte by byte, while the matching forget, [Mmap.brk_unmaps], is
    page-rounded to [[page_round_up_Z r, page_round_up_Z b)].  For [r] not
    page aligned the lazy bytes in [[r, page_round_up_Z r)] therefore lose
    their owner and nothing forgets them, so BYTE ownership is NOT
    inductive under a same-page [brk] shrink.  The page floor survives
    because a byte-granular cut removes an ALIGNED byte only when its whole
    page lies inside the forgotten range; [brk_floor_outside] is that
    argument, proved rather than assumed.

    WHAT THIS INVARIANT DOES NOT GIVE, as a lemma rather than a comment,
    because a convention is not a check: [WF_gives_no_unaligned_byte_owner]
    -- there is no owner for an UNALIGNED lazy byte after a same-page [brk]
    shrink, and that is deliberate.

    [NoaccessOwned] proves the first conjunct already
    ([init_model_sys_inv], [check_syscall_preserves_sys_inv],
    [syscall_spec_preserves_sys_inv], [sstep_preserves_sys_inv],
    [star_cfg_preserves_sys_inv]); nothing here re-proves it.  Each arm
    below takes [VmMapsDisjoint.check_*_preserves],
    [MapsFit.check_*_preserves_fit] and
    [NoaccessOwned.check_*_preserves_na] for it and proves only the two
    ledger conjuncts.

    Proved by LpsImpact.RevFixLibdiginet.WfWriterArms for OSSV-266, first
    against LPS 6692dfb5 in the proof fork
    (theorem-labs/oss-verify-proofs-internal, branch
    lps-revision/libreac-wf), and lifted here. *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import VmMapsDisjoint.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require MapsFit NoaccessOwned Placement BudgetPremise.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import
  Mm.Mmap Mm.Mremap Mm.Mprotect.
Import ListNotations.
Open Scope Z_scope. Open Scope bv_scope.
Set Default Proof Mode "Classic".

Definition LZ_OWNED (m : Model) : Prop :=
forall a n x, In (a, n) (m_vm_lazy m) ->
(bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
NoaccessOwned.owned (vm_maps (m_vmmaps m)) (page_round_down_Z x).

Definition MAT_OWNED (m : Model) : Prop :=
forall p, In p (m_vm_materialized m) ->
(bv_unsigned p mod page_size = 0)%Z
/\ NoaccessOwned.owned (vm_maps (m_vmmaps m)) (bv_unsigned p).

Definition WF (m : Model) : Prop :=
NoaccessOwned.sys_inv (m_vmmaps m) /\ LZ_OWNED m /\ MAT_OWNED m.

(* One equation frames all three ledgers, because [m_vmmaps], [m_vm_lazy]
   and [m_vm_materialized] are three projections of one [Model] field,
   [m_vm].  So an arm that leaves [m_vm] alone preserves [WF] outright.
   NOTE: the [check_*_frame] family gives only [m_vmmaps m' = m_vmmaps m],
   which is NOT enough for the two ledger conjuncts. *)
Lemma WF_of_vm_eq : forall m m', m_vm m' = m_vm m -> WF m -> WF m'.
Proof.
intros m m' E HW.
unfold WF, LZ_OWNED, MAT_OWNED, m_vmmaps, m_vm_lazy, m_vm_materialized in *.
rewrite E. exact HW.
Qed.

(* ------------------------------------------------------------------ *)
(* THE INITIAL STATE.  The two backing ledgers of [State.init_model] are
   [[]]: [mkModel] builds [mkVmState vm [] []] and [init_model] reaches
   that record only through [with_creds], [with_urandom], [with_net],
   [with_nofile], [with_sigmask] and [with_abort_terminal], none of which
   touches [m_vm].  Stated as conversions rather than left to a tactic,
   because [State.v] declares the accessors and setters [simpl never]. *)
(* ------------------------------------------------------------------ *)

Lemma init_lazy_nil : forall segs pc ph sp brk0 mbase rnd lim inp,
m_vm_lazy (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp)) = [].
Proof. intros. reflexivity. Qed.

Lemma init_mat_nil : forall segs pc ph sp brk0 mbase rnd lim inp,
m_vm_materialized (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp)) = [].
Proof. intros. reflexivity. Qed.

Theorem init_config_WF : forall segs pc ph sp brk0 mbase rnd lim inp,
WF (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp)).
Proof.
intros segs pc ph sp brk0 mbase rnd lim inp. unfold WF. split; [| split].
- exact (NoaccessOwned.init_config_sys_inv segs pc ph sp brk0 mbase rnd lim inp).
- intros a n x Hin _.
  rewrite (init_lazy_nil segs pc ph sp brk0 mbase rnd lim inp) in Hin.
  destruct Hin.
- intros p Hin.
  rewrite (init_mat_nil segs pc ph sp brk0 mbase rnd lim inp) in Hin.
  destruct Hin.
Qed.

(* ------------------------------------------------------------------ *)
(* Page-floor arithmetic.  [page_size] is 4096 and [page_round_down_Z n]
   is [n / page_size * page_size] (LPS 6692dfb5, State.v). *)
(* ------------------------------------------------------------------ *)

Lemma two64_mod : (2 ^ 64 mod page_size = 0)%Z.
Proof. reflexivity. Qed.

Lemma pfloor_bounds : forall x, (0 <= x)%Z ->
(page_round_down_Z x <= x < page_round_down_Z x + page_size)%Z.
Proof.
intros x Hx. unfold page_round_down_Z, page_size.
pose proof (Z.div_mod x 4096 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound x 4096 ltac:(lia)) as B. lia.
Qed.

Lemma pfloor_nonneg : forall x, (0 <= x)%Z -> (0 <= page_round_down_Z x)%Z.
Proof.
intros x H. unfold page_round_down_Z, page_size.
pose proof (Z.div_pos x 4096 H ltac:(lia)). nia.
Qed.

Lemma pfloor_mod : forall x, (page_round_down_Z x mod page_size = 0)%Z.
Proof. intros x. unfold page_round_down_Z, page_size. apply Z.mod_mul. lia. Qed.

Lemma pfloor_mono_lo : forall lo x, (lo mod page_size = 0)%Z -> (0 <= lo)%Z ->
(lo <= x)%Z -> (lo <= page_round_down_Z x)%Z.
Proof.
intros lo x Hlo H0 Hle. unfold page_round_down_Z, page_size in *.
destruct (Z.mod_divide lo 4096 ltac:(lia)) as [Hd _].
destruct (Hd Hlo) as [k Hk]. subst lo.
assert (Hq : (k <= x / 4096)%Z) by (apply Z.div_le_lower_bound; lia).
nia.
Qed.

Lemma pup_mod : forall n, (page_round_up_Z n mod page_size = 0)%Z.
Proof. intros n. unfold page_round_up_Z, page_size. apply Z.mod_mul. lia. Qed.

Lemma pup_ge : forall n, (n <= page_round_up_Z n)%Z.
Proof.
intros n. unfold page_round_up_Z, page_size.
pose proof (Z.div_mod (n + 4096 - 1) 4096 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (n + 4096 - 1) 4096 ltac:(lia)) as B. lia.
Qed.

Lemma aligned_ge_pup : forall n y, (y mod page_size = 0)%Z -> (0 <= y)%Z ->
(n <= y)%Z -> (page_round_up_Z n <= y)%Z.
Proof.
intros n y Hy H0 Hle. unfold page_round_up_Z, page_size in *.
destruct (Z.mod_divide y 4096 ltac:(lia)) as [Hd _].
destruct (Hd Hy) as [k Hk]. subst y.
assert (Hq : ((n + 4096 - 1) / 4096 < k + 1)%Z)
  by (apply Z.div_lt_upper_bound; lia).
nia.
Qed.

Lemma aligned_lt_step : forall y z, (y mod page_size = 0)%Z ->
(z mod page_size = 0)%Z -> (y < z)%Z -> (y + page_size <= z)%Z.
Proof.
intros y z Hy Hz H. unfold page_size in *.
destruct (Z.mod_divide y 4096 ltac:(lia)) as [Hd _]. destruct (Hd Hy) as [a Ha].
destruct (Z.mod_divide z 4096 ltac:(lia)) as [He _]. destruct (He Hz) as [b Hb].
subst. nia.
Qed.

(* A PAGE-ALIGNED range swallows the whole page of any byte whose floor it
   contains.  This is the step that makes the floor inductive where the byte
   is not: see brk_floor_outside below. *)
Lemma byte_in_aligned_range : forall lo hi x,
(lo mod page_size = 0)%Z -> (hi mod page_size = 0)%Z -> (0 <= lo)%Z ->
(0 <= x)%Z -> (lo <= page_round_down_Z x < hi)%Z -> (lo <= x < hi)%Z.
Proof.
intros lo hi x Hlo Hhi H0 Hx [H1 H2].
pose proof (pfloor_bounds x Hx) as [B1 B2].
pose proof (aligned_lt_step _ _ (pfloor_mod x) Hhi H2). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The inverse of [NoaccessOwned.owned_subtract]: a byte the cut list still
   covers was covered before and lies outside the cut.  LPS has the forward
   direction only. *)
(* ------------------------------------------------------------------ *)

Lemma iv_subtract_owned_inv : forall a sz lo hi x,
(0 <= lo)%Z -> (lo <= hi)%Z ->
(bv_unsigned a + bv_unsigned sz <= 2 ^ 64)%Z ->
NoaccessOwned.owned (iv_subtract a sz lo hi) x ->
(bv_unsigned a <= x < bv_unsigned a + bv_unsigned sz)%Z /\ ~ (lo <= x < hi)%Z.
Proof.
intros a sz lo hi x Hlo Hlh Hfit (b & s & Hin & Hx).
pose proof (word_range a) as Ra. pose proof (word_range sz) as Rs.
unfold iv_subtract in Hin. cbv zeta in Hin.
apply in_app_or in Hin. destruct Hin as [Hin|Hin].
- destruct (Z.ltb_spec (bv_unsigned a) lo) as [Hc|Hc]; cbn [In] in Hin;
    [|destruct Hin].
  destruct Hin as [Heq|[]]. injection Heq as <- <-.
  rewrite u64 in Hx by lia. lia.
- destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Hc|Hc];
    cbn [In] in Hin; [|destruct Hin].
  destruct Hin as [Heq|[]]. injection Heq as <- <-.
  rewrite !u64 in Hx by lia. lia.
Qed.

Lemma owned_subtract_inv : forall maps lo hi x,
(0 <= lo)%Z -> (lo <= hi)%Z -> MapsFit.maps_fit maps ->
NoaccessOwned.owned (maps_subtract maps lo hi) x ->
NoaccessOwned.owned maps x /\ ~ (lo <= x < hi)%Z.
Proof.
induction maps as [|[a s] r IH]; intros lo hi x Hlo Hlh Hf Ho.
- destruct Ho as (b & t & [] & _).
- destruct Ho as (b & t & Hin & Hx). cbn [maps_subtract] in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  + assert (Hfit : (bv_unsigned a + bv_unsigned s <= 2 ^ 64)%Z).
    { pose proof (Hf a s (or_introl eq_refl)) as Hb.
      unfold two_pow_64 in Hb. exact Hb. }
    destruct (iv_subtract_owned_inv a s lo hi x Hlo Hlh Hfit
                (ex_intro _ b (ex_intro _ t (conj Hin Hx)))) as [H1 H2].
    split; [exists a, s; split; [left; reflexivity | exact H1] | exact H2].
  + destruct (IH lo hi x Hlo Hlh
                (fun c u Hcu => Hf c u (or_intror Hcu))
                (ex_intro _ b (ex_intro _ t (conj Hin Hx)))) as [H1 H2].
    split; [apply NoaccessOwned.owned_cons; exact H1 | exact H2].
Qed.

(* ------------------------------------------------------------------ *)
(* WHAT THE INVARIANT GIVES THAT IT DOES NOT STATE.  [WF] carries
   [MapsFit.vm_fit] of the MAPPING ledger inside [sys_inv]; it says nothing
   at all about the LAZY ledger's entries, and yet it bounds them, because a
   lazy byte at or above 2^64 could have no owner and [LZ_OWNED] demands
   one.  [WF_lazy_fit] is that argument, and the cut lemmas below need it. *)
(* ------------------------------------------------------------------ *)

Lemma WF_maps_fit : forall m, WF m -> MapsFit.maps_fit (vm_maps (m_vmmaps m)).
Proof. intros m HW. exact (proj1 (proj2 (proj1 HW))). Qed.

Lemma owned_lt_two64 : forall maps y,
MapsFit.maps_fit maps -> NoaccessOwned.owned maps y -> (y < 2 ^ 64)%Z.
Proof.
intros maps y Hf (b & s & Hin & Hy).
pose proof (Hf b s Hin) as Hb. unfold two_pow_64 in Hb. lia.
Qed.

Lemma WF_lazy_fit : forall m, WF m -> MapsFit.maps_fit (m_vm_lazy m).
Proof.
intros m HW a n Hin. unfold two_pow_64.
pose proof (word_range a) as Ra. pose proof (word_range n) as Rn.
destruct (Z.eq_dec (bv_unsigned n) 0) as [Hz|Hz]; [lia|].
set (x := (bv_unsigned a + bv_unsigned n - 1)%Z).
assert (Hx : (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z)
  by (subst x; lia).
assert (H0 : (0 <= x)%Z) by (subst x; lia).
pose proof (proj1 (proj2 HW) a n x Hin Hx) as Hown.
pose proof (owned_lt_two64 _ _ (WF_maps_fit m HW) Hown) as Hlt.
pose proof (aligned_lt_step _ _ (pfloor_mod x) two64_mod Hlt) as Hstep.
pose proof (pfloor_bounds x H0) as [B1 B2]. subst x. unfold page_size in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* THE CUT ARM.  [vm_forget_range lo hi] on the backing ledgers beside a
   [maps_subtract _ lo hi] on the mapping ledger, over the SAME range, with
   that range page aligned.  munmap and the two mmap destroy arms are this. *)
(* ------------------------------------------------------------------ *)

Lemma ledger_cut_aligned : forall m MP lo hi,
WF m ->
(0 <= lo)%Z -> (lo <= hi)%Z ->
(lo mod page_size = 0)%Z -> (hi mod page_size = 0)%Z ->
(forall y, NoaccessOwned.owned (maps_subtract (vm_maps (m_vmmaps m)) lo hi) y ->
           NoaccessOwned.owned MP y) ->
(forall a n x, In (a, n) (maps_subtract (m_vm_lazy m) lo hi) ->
   (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
   NoaccessOwned.owned MP (page_round_down_Z x))
/\ (forall p, In p (List.filter (page_outside_range lo hi) (m_vm_materialized m)) ->
   (bv_unsigned p mod page_size = 0)%Z /\ NoaccessOwned.owned MP (bv_unsigned p)).
Proof.
intros m MP lo hi HW Hlo Hlh Hal Hah Hmono. split.
- intros a n x Hin Hx.
  assert (H0 : (0 <= x)%Z) by (pose proof (word_range a); lia).
  destruct (owned_subtract_inv _ lo hi x Hlo Hlh (WF_lazy_fit m HW)
              (ex_intro _ a (ex_intro _ n (conj Hin Hx)))) as [Hol Hout].
  destruct Hol as (a0 & n0 & Hin0 & Hx0).
  pose proof (proj1 (proj2 HW) a0 n0 x Hin0 Hx0) as Hown.
  apply Hmono. apply NoaccessOwned.owned_subtract;
    [exact (WF_maps_fit m HW) | exact Hown |].
  intros Hc. apply Hout. exact (byte_in_aligned_range lo hi x Hal Hah Hlo H0 Hc).
- intros p Hin. apply List.filter_In in Hin as [Hin Hout].
  destruct (proj2 (proj2 HW) p Hin) as [Hpa Hown].
  split; [exact Hpa|]. apply Hmono.
  apply NoaccessOwned.owned_subtract; [exact (WF_maps_fit m HW) | exact Hown |].
  unfold page_outside_range in Hout. apply negb_true_iff in Hout.
  apply andb_false_iff in Hout.
  intros [H1 H2]. destruct Hout as [E|E];
    [apply Z.leb_nle in E | apply Z.ltb_nlt in E]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* munmap.  Post-state [with_mmap_destroyed addr n h' m] is
   [vm_forget_range addr (addr+n) (with_vmmaps h' m)] with
   [h' = mmap_fixed_destroyed_next (m_vmmaps m) addr n], whose [vm_maps] is
   [maps_subtract (vm_maps (m_vmmaps m)) addr (addr+n)] (LPS 6692dfb5,
   Sys/Mm/Mmap.v).  The checker's own gates give the alignment: [addr] is
   page aligned and [n] is a [page_round_up_Z] value. *)
(* ------------------------------------------------------------------ *)

Lemma check_munmap_ledger : forall addr len eff m m' evs,
check_munmap addr len eff m = CheckOk m' evs -> WF m ->
LZ_OWNED m' /\ MAT_OWNED m'.
Proof.
intros addr len [ret ws zs us cs ci] m m' evs H HW.
unfold check_munmap in H. cbv zeta in H.
pose proof (word_range addr) as Ra. pose proof (word_range len) as Rl.
destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len) eqn:Eg.
{ apply check_ret_only_model in H. subst m'. exact (conj (proj1 (proj2 HW)) (proj2 (proj2 HW))). }
apply orb_false_iff in Eg as [Ealign Elen].
apply negb_false_iff, Z.eqb_eq in Ealign.
pose proof (w_is0_false len Elen) as Hlen0.
assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z)
  by (apply page_round_up_pos; lia).
destruct (TASK_SIZE <? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z eqn:Etop.
{ apply check_ret_only_model in H. subst m'. exact (conj (proj1 (proj2 HW)) (proj2 (proj2 HW))). }
apply Z.ltb_ge in Etop.
assert (Htask : (TASK_SIZE < 2 ^ 64)%Z) by (unfold TASK_SIZE; lia).
assert (Hn : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
             = page_round_up_Z (bv_unsigned len))
  by (apply u64; unfold TASK_SIZE in *; lia).
assert (Hmod : (page_round_up_Z (bv_unsigned len) mod page_size = 0)%Z)
  by apply pup_mod.
assert (KEY : forall h'', vm_maps h'' = maps_subtract (vm_maps (m_vmmaps m))
                 (bv_unsigned addr)
                 (bv_unsigned addr + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) ->
  LZ_OWNED (vm_forget_range (bv_unsigned addr)
              (bv_unsigned addr + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
              (with_vmmaps h'' m))
  /\ MAT_OWNED (vm_forget_range (bv_unsigned addr)
              (bv_unsigned addr + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
              (with_vmmaps h'' m))).
{ intros h'' Hh.
  destruct (ledger_cut_aligned m (vm_maps h'')
              (bv_unsigned addr)
              (bv_unsigned addr + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
              HW ltac:(lia) ltac:(rewrite Hn; lia)
              ltac:(exact Ealign)
              ltac:(rewrite Hn; apply NoaccessOwned.aligned_add; [exact Ealign | exact Hmod])
              ltac:(rewrite Hh; intros y Hy; exact Hy)) as [HL HM].
  split; [exact HL | exact HM]. }
destruct (map_has (vm_maps (m_vmmaps m)) addr
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Ehas.
- destruct ws, zs, cs, ci; try discriminate.
  destruct (errno_ret_in munmap_errnos ret) eqn:Eerr.
  + destruct us; [|discriminate]. injection H as <- <-.
    exact (conj (proj1 (proj2 HW)) (proj2 (proj2 HW))).
  + destruct (w_is0 ret && listNN_eqb us
                [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]) eqn:Eok;
      [|discriminate].
    injection H as <- <-. unfold with_mmap_destroyed. apply KEY. reflexivity.
- destruct (munmap_free_ok (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len))) eqn:Efree.
  { apply check_ret_only_model in H. subst m'.
    exact (conj (proj1 (proj2 HW)) (proj2 (proj2 HW))). }
  destruct (munmap_cut_ok (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len))) eqn:Ecut;
    [|discriminate].
  destruct ws, zs, cs, ci; try discriminate.
  destruct (errno_ret_in munmap_errnos ret) eqn:Eerr.
  + destruct us; [|discriminate]. injection H as <- <-.
    exact (conj (proj1 (proj2 HW)) (proj2 (proj2 HW))).
  + destruct (w_is0 ret && listNN_eqb us
                [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]) eqn:Eok;
      [|discriminate].
    injection H as <- <-. unfold with_mmap_destroyed. apply KEY. reflexivity.
Qed.

Lemma check_munmap_WF : forall addr len eff m m' evs,
check_munmap addr len eff m = CheckOk m' evs -> WF m -> WF m'.
Proof.
intros addr len eff m m' evs H HW.
destruct (check_munmap_ledger _ _ _ _ _ _ H HW) as [HL HM].
destruct (proj1 HW) as (Hwf & Hfit & Hna).
split; [|exact (conj HL HM)].
split; [exact (check_munmap_preserves _ _ _ _ _ _ H Hwf)|].
split; [exact (MapsFit.check_munmap_preserves_fit _ _ _ _ _ _ H Hfit)|].
exact (NoaccessOwned.check_munmap_preserves_na _ _ _ _ _ _ H Hwf Hfit Hna).
Qed.

(* ------------------------------------------------------------------ *)
(* An arm that leaves the mapping ledger and both backing ledgers alone.
   mprotect is this: mprotect_model_next rebuilds VmMaps with vm_maps
   unchanged and touches no backing (LPS 6692dfb5, Sys/Mm/Mprotect.v). *)
(* ------------------------------------------------------------------ *)

Lemma ledger_of_maps_eq : forall m m',
vm_maps (m_vmmaps m') = vm_maps (m_vmmaps m) ->
m_vm_lazy m' = m_vm_lazy m ->
m_vm_materialized m' = m_vm_materialized m ->
LZ_OWNED m -> MAT_OWNED m -> LZ_OWNED m' /\ MAT_OWNED m'.
Proof.
intros m m' Hm Hl Ht HL HM. unfold LZ_OWNED, MAT_OWNED in *.
rewrite Hm, Hl, Ht. exact (conj HL HM).
Qed.

Lemma check_mprotect_ledger : forall addr len prot eff m m' evs,
check_mprotect addr len prot eff m = CheckOk m' evs -> WF m ->
LZ_OWNED m' /\ MAT_OWNED m'.
Proof.
intros addr len prot [ret ws zs us cs ci] m m' evs H HW.
unfold check_mprotect in H. cbv zeta in H.
pose proof (proj1 (proj2 HW)) as HL. pose proof (proj2 (proj2 HW)) as HM.
repeat (match type of H with
        | check_ret_only _ _ _ _ = CheckOk _ _ =>
            apply check_ret_only_model in H; subst m'; exact (conj HL HM)
        | CheckReject = CheckOk _ _ => discriminate H
        | CheckUnmodeled = CheckOk _ _ => discriminate H
        | context [ if ?b then _ else _ ] => destruct b eqn:?
        | context [ match ?x with _ => _ end ] => destruct x eqn:?
        end);
  try discriminate H; injection H as <- <-;
  try exact (conj HL HM);
  apply (ledger_of_maps_eq m); try reflexivity; try exact HL; try exact HM.
Qed.

Lemma check_mprotect_WF : forall addr len prot eff m m' evs,
check_mprotect addr len prot eff m = CheckOk m' evs -> WF m -> WF m'.
Proof.
intros addr len prot eff m m' evs H HW.
destruct (check_mprotect_ledger _ _ _ _ _ _ _ H HW) as [HL HM].
destruct (proj1 HW) as (Hwf & Hfit & Hna).
split; [|exact (conj HL HM)].
split; [exact (check_mprotect_preserves _ _ _ _ _ _ _ H Hwf)|].
split; [exact (MapsFit.check_mprotect_preserves_fit _ _ _ _ _ _ _ H Hfit)|].
exact (NoaccessOwned.check_mprotect_preserves_na _ _ _ _ _ _ _ H Hwf Hfit Hna).
Qed.

(* ------------------------------------------------------------------ *)
(* THE brk ARM, AND WHY THE FLOOR IS THE FLOOR.

   A brk shrink cuts the MAPPING ledger byte by byte over [[r, b)]
   (Mmap.brk_maps_next) and then over the whole pages the kernel unmaps
   (Mmap.brk_unmap_cut), while the FORGET that accompanies it is
   page-rounded: [Mmap.brk_unmaps] is [[page_round_up_Z r,
   page_round_up_Z b)].  For [r] not page aligned the lazy bytes in
   [[r, page_round_up_Z r)] therefore lose their owner and nothing
   forgets them, so BYTE ownership is not inductive here.

   [brk_floor_outside] is the step that saves the FLOOR, and it is the
   reason the invariant is spelled on the page floor rather than the
   byte.  It says: an ALIGNED address the forget did not remove is also
   outside the byte-granular cut.  Proved, not assumed. *)
(* ------------------------------------------------------------------ *)

Lemma brk_floor_outside : forall r b y,
(0 <= r)%Z -> (0 <= b)%Z -> (0 <= y)%Z -> (y mod page_size = 0)%Z ->
~ (page_round_up_Z r <= y < page_round_up_Z b)%Z ->
~ (r <= y < b)%Z.
Proof.
intros r b y Hr Hb Hy Hal Hout [H1 H2]. apply Hout. split.
- exact (aligned_ge_pup r y Hal Hy H1).
- pose proof (pup_ge b). lia.
Qed.

(* The invariant NO LONGER GUARANTEES an owner for an unaligned lazy byte
   after a same-page brk shrink, and that is deliberate.  Stated as a
   lemma so a reader meets the boundary where it is, rather than a
   comment nothing checks: what survives is exactly the floor. *)
Lemma WF_gives_no_unaligned_byte_owner : forall m a n x,
WF m -> In (a, n) (m_vm_lazy m) ->
(bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
NoaccessOwned.owned (vm_maps (m_vmmaps m)) (page_round_down_Z x)
/\ (page_round_down_Z x <= x < page_round_down_Z x + page_size)%Z.
Proof.
intros m a n x HW Hin Hx.
assert (H0 : (0 <= x)%Z) by (pose proof (word_range a); lia).
split; [exact (proj1 (proj2 HW) a n x Hin Hx) | exact (pfloor_bounds x H0)].
Qed.

(* The general shape: forget a PAGE-ALIGNED range on both backing ledgers,
   and transport every aligned owner the forget did not remove into the new
   mapping ledger.  brk is this with the two nested cuts as the transport;
   so is any future arm whose forget is page-rounded. *)
Lemma ledger_forget_sub : forall m MP lo hi,
WF m ->
(0 <= lo)%Z -> (lo <= hi)%Z ->
(lo mod page_size = 0)%Z -> (hi mod page_size = 0)%Z ->
(forall y, NoaccessOwned.owned (vm_maps (m_vmmaps m)) y ->
           (y mod page_size = 0)%Z -> (0 <= y)%Z -> ~ (lo <= y < hi)%Z ->
           NoaccessOwned.owned MP y) ->
(forall a n x, In (a, n) (maps_subtract (m_vm_lazy m) lo hi) ->
   (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
   NoaccessOwned.owned MP (page_round_down_Z x))
/\ (forall p, In p (List.filter (page_outside_range lo hi) (m_vm_materialized m)) ->
   (bv_unsigned p mod page_size = 0)%Z /\ NoaccessOwned.owned MP (bv_unsigned p)).
Proof.
intros m MP lo hi HW Hlo Hlh Hal Hah Htr. split.
- intros a n x Hin Hx.
  assert (H0 : (0 <= x)%Z) by (pose proof (word_range a); lia).
  destruct (owned_subtract_inv _ lo hi x Hlo Hlh (WF_lazy_fit m HW)
              (ex_intro _ a (ex_intro _ n (conj Hin Hx)))) as [Hol Hout].
  destruct Hol as (a0 & n0 & Hin0 & Hx0).
  pose proof (proj1 (proj2 HW) a0 n0 x Hin0 Hx0) as Hown.
  pose proof (pfloor_bounds x H0) as [B1 B2].
  apply Htr; [exact Hown | apply pfloor_mod | apply pfloor_nonneg; lia |].
  intros Hc. apply Hout. exact (byte_in_aligned_range lo hi x Hal Hah Hlo H0 Hc).
- intros p Hin. apply List.filter_In in Hin as [Hin Hout].
  destruct (proj2 (proj2 HW) p Hin) as [Hpa Hown].
  pose proof (word_range p) as Rp.
  split; [exact Hpa|]. apply Htr; [exact Hown | exact Hpa | lia |].
  unfold page_outside_range in Hout. apply negb_true_iff in Hout.
  apply andb_false_iff in Hout.
  intros [H1 H2]. destruct Hout as [E|E];
    [apply Z.leb_nle in E | apply Z.ltb_nlt in E]; lia.
Qed.

(* [page_round_up_Z] of a word address stays inside [0, 2^64]: the bound the
   inner cut of [brk_unmap_cut] needs, because its upper end is
   [Z.min hi (two_pow_64 - 1)].  Not in LPS at 6692dfb5; the same obligation
   was met independently by LpsImpact.RevFixReacPw's reac-repacer lane. *)
Lemma pup_le_two64 : forall x, (0 <= x < 2 ^ 64)%Z ->
(0 <= page_round_up_Z x <= 2 ^ 64)%Z.
Proof.
intros x Hx. unfold page_round_up_Z, page_size.
assert (HQ : ((2 ^ 64 + 4096 - 1) / 4096 = 2 ^ 52)%Z) by (vm_compute; reflexivity).
pose proof (Z.div_le_mono (x + 4096 - 1) (2 ^ 64 + 4096 - 1) 4096 ltac:(lia) ltac:(lia)).
pose proof (Z.div_pos (x + 4096 - 1) 4096 ltac:(lia) ltac:(lia)).
lia.
Qed.

Lemma pup_mono : forall a b, (a <= b)%Z -> (page_round_up_Z a <= page_round_up_Z b)%Z.
Proof.
intros a b H. unfold page_round_up_Z, page_size.
pose proof (Z.div_le_mono (a + 4096 - 1) (b + 4096 - 1) 4096 ltac:(lia) ltac:(lia)).
nia.
Qed.

(* The whole of the brk shrink's mapping-ledger transport: an aligned owner
   the page-rounded forget did not remove survives BOTH cuts of
   [brk_maps_next] -- the byte-granular [[r, b)] and the page-rounded one.
   The first is [brk_floor_outside]; the second is immediate because the
   inner cut's range is contained in the forgotten one. *)
Lemma brk_maps_next_owned : forall h req r y,
MapsFit.maps_fit (vm_maps h) ->
(0 <= y)%Z -> (y mod page_size = 0)%Z ->
~ (page_round_up_Z (bv_unsigned r) <= y < page_round_up_Z (bv_unsigned (vm_brk h)))%Z ->
NoaccessOwned.owned (vm_maps h) y ->
NoaccessOwned.owned (brk_maps_next h req r) y.
Proof.
intros h req r y Hfit H0 Hal Hout Hown.
pose proof (word_range r) as Rr. pose proof (word_range (vm_brk h)) as Rb.
pose proof (pup_le_two64 _ Rr) as PRr.
pose proof (pup_le_two64 _ Rb) as PRb.
unfold brk_maps_next.
destruct (Z.ltb 0 (bv_unsigned (vm_brk h))
          && Z.ltb (bv_unsigned r) (bv_unsigned (vm_brk h))) eqn:Eshrink.
- (* PROVISIONAL, LpsMmPrecision: this file belongs to
     LpsImpact.RevFixLibdiginet.WfWriterArms and its text wins.  The brk
     shrink no longer cuts [[r, b)] out of [vm_maps] — it takes only the
     pages [Mmap.brk_unmaps] names — so the [owned_subtract] step over
     the byte range has nothing to apply to and [Hown] carries straight
     through the empty case.  [brk_floor_outside] still discharges the
     page-rounded cut. *)
  unfold brk_unmap_cut. cbv zeta.
  destruct (Z.ltb (page_round_up_Z (bv_unsigned r))
                  (page_round_up_Z (bv_unsigned (vm_brk h)))) eqn:Ecut;
    [|exact Hown].
  apply Z.ltb_lt in Ecut.
  apply NoaccessOwned.owned_subtract;
    [ exact Hfit | exact Hown |].
  intros [H1 H2]. apply Hout. split; [exact H1 | lia].
- apply NoaccessOwned.owned_app_r. exact Hown.
Qed.

Lemma check_brk_ledger : forall req eff m m' evs,
check_brk req eff m = CheckOk m' evs -> WF m -> LZ_OWNED m' /\ MAT_OWNED m'.
Proof.
intros req [ret ws zs us cs ci] m m' evs H HW.
unfold check_brk in H.
destruct ws as [|? ?]; [|discriminate].
destruct cs as [|? ?]; [|discriminate].
destruct ci as [|? ?]; [|discriminate].
destruct (brk_r_ok m req ret
&& listNN_eqb zs (brk_zeros req ret (vm_brk (m_vmmaps m)))
&& listNN_eqb us (brk_unmaps ret (vm_brk (m_vmmaps m)))) eqn:E; [|discriminate].
injection H as <- <-.
(* The one corner [brk_unmaps] cannot convert losslessly is [lo = 0] with
   [hi = 2^64], and LPS's own comment says no [brk_r_ok] resolution admits it.
   Here is that argument: [brk_r_ok_cases] gives either the unmoved break --
   and then the two page-rounded ends coincide, so there is nothing to forget
   -- or [r = req] with [req] nonzero, which puts [page_round_up_Z r] above 0. *)
assert (HRET : bv_unsigned ret = bv_unsigned (vm_brk (m_vmmaps m))
               \/ (0 < bv_unsigned ret)%Z).
{ apply andb_true_iff in E as [E0 _]. apply andb_true_iff in E0 as [Hok _].
  destruct (NoaccessOwned.brk_r_ok_cases m req ret Hok) as [Hre|[Hre Hreq]].
  - left. rewrite Hre. reflexivity.
  - right. pose proof (w_is0_false req Hreq) as Hq.
    pose proof (word_range req). rewrite Hre. lia. }
set (h := m_vmmaps m) in *.
set (loP := page_round_up_Z (bv_unsigned ret)) in *.
set (hiP := page_round_up_Z (bv_unsigned (vm_brk h))) in *.
pose proof (word_range ret) as Rr. pose proof (word_range (vm_brk h)) as Rb.
pose proof (pup_le_two64 _ Rr) as PRr. pose proof (pup_le_two64 _ Rb) as PRb.
assert (HloP : loP = page_round_up_Z (bv_unsigned ret)) by reflexivity.
assert (HhiP : hiP = page_round_up_Z (bv_unsigned (vm_brk h))) by reflexivity.
assert (HalLo : (loP mod page_size = 0)%Z) by (rewrite HloP; apply pup_mod).
assert (HalHi : (hiP mod page_size = 0)%Z) by (rewrite HhiP; apply pup_mod).
assert (HFIT : MapsFit.maps_fit (vm_maps h)) by exact (WF_maps_fit m HW).
(* The transport, stated once and used by both shapes of the forget. *)
assert (TR : forall y, NoaccessOwned.owned (vm_maps h) y ->
             (y mod page_size = 0)%Z -> (0 <= y)%Z -> ~ (loP <= y < hiP)%Z ->
             NoaccessOwned.owned (vm_maps (brk_model_next h req ret)) y).
{ intros y Hy Hal Hy0 Hout. cbn [vm_maps].
  exact (brk_maps_next_owned h req ret y HFIT Hy0 Hal Hout Hy). }
unfold with_brk_next. fold h. unfold brk_unmaps. cbv zeta. fold loP hiP.
destruct (Z.ltb 0 (bv_unsigned (vm_brk h))) eqn:Eb; unfold brk_page_range; cbv zeta.
- destruct (Z.ltb loP hiP) eqn:Ecut.
  + apply Z.ltb_lt in Ecut.
    assert (Hpos : (0 < loP)%Z).
    { destruct HRET as [Heq|Hpos].
      - exfalso.
        assert (loP = hiP) by (rewrite HloP, HhiP; fold h; rewrite Heq; reflexivity).
        lia.
      - pose proof (pup_ge (bv_unsigned ret)) as Hge. rewrite HloP. lia. }
    assert (HL : bv_unsigned (Z_to_bv 64 loP) = loP) by (apply u64; lia).
    assert (HN : bv_unsigned (Z_to_bv 64 (hiP - loP)) = (hiP - loP)%Z)
      by (apply u64; lia).
    cbn [forget_vm_ranges]. rewrite HL, HN.
    replace (loP + (hiP - loP))%Z with hiP by lia.
    destruct (ledger_forget_sub m (vm_maps (brk_model_next h req ret)) loP hiP
                HW ltac:(lia) ltac:(lia) HalLo HalHi TR) as [HLz HMt].
    split; [exact HLz | exact HMt].
  + apply Z.ltb_ge in Ecut. cbn [forget_vm_ranges].
    split.
    * intros a n x Hin Hx. cbn [m_vm_lazy] in Hin.
      assert (H0 : (0 <= x)%Z) by (pose proof (word_range a); lia).
      pose proof (proj1 (proj2 HW) a n x Hin Hx) as Hown.
      apply TR; [exact Hown | apply pfloor_mod | apply pfloor_nonneg; lia | lia].
    * intros p Hin. cbn [m_vm_materialized] in Hin.
      destruct (proj2 (proj2 HW) p Hin) as [Hpa Hown].
      pose proof (word_range p) as Rp.
      split; [exact Hpa|]. apply TR; [exact Hown | exact Hpa | lia | lia].
- cbn [forget_vm_ranges].
  split.
  + intros a n x Hin Hx. cbn [m_vm_lazy] in Hin.
    assert (H0 : (0 <= x)%Z) by (pose proof (word_range a); lia).
    pose proof (proj1 (proj2 HW) a n x Hin Hx) as Hown.
    apply Z.ltb_ge in Eb.
    apply TR; [exact Hown | apply pfloor_mod | apply pfloor_nonneg; lia |].
    assert (Hz : hiP = 0%Z)
      by (rewrite HhiP; replace (bv_unsigned (vm_brk h)) with 0%Z by lia;
          unfold page_round_up_Z, page_size; reflexivity).
    pose proof (pfloor_nonneg x H0). lia.
  + intros p Hin. cbn [m_vm_materialized] in Hin.
    destruct (proj2 (proj2 HW) p Hin) as [Hpa Hown].
    pose proof (word_range p) as Rp. apply Z.ltb_ge in Eb.
    split; [exact Hpa|]. apply TR; [exact Hown | exact Hpa | lia |].
    assert (Hz : hiP = 0%Z)
      by (rewrite HhiP; replace (bv_unsigned (vm_brk h)) with 0%Z by lia;
          unfold page_round_up_Z, page_size; reflexivity).
    lia.
Qed.

Lemma check_brk_WF : forall req eff m m' evs,
check_brk req eff m = CheckOk m' evs -> WF m -> WF m'.
Proof.
intros req eff m m' evs H HW.
destruct (check_brk_ledger _ _ _ _ _ H HW) as [HL HM].
destruct (proj1 HW) as (Hwf & Hfit & Hna).
split; [|exact (conj HL HM)].
split; [exact (check_brk_preserves _ _ _ _ _ H Hwf)|].
split; [exact (MapsFit.check_brk_preserves_fit _ _ _ _ _ H Hfit)|].
exact (NoaccessOwned.check_brk_preserves_na _ _ _ _ _ H Hwf Hfit Hna).
Qed.

(* ------------------------------------------------------------------ *)
(* THE ADD SHAPE.  mmap and mremap install a fresh mapping [(A, N)] at the
   head of the ledger and, under MAP_NORESERVE, record its page-aligned
   interior in the lazy ledger ([State.vm_add_lazy], [State.lazy_interior]).
   The interior is where the floor pays for itself again: the recorded
   range is the INTERIOR, so every byte of it has its whole page inside
   [[A, A+N)]. *)
(* ------------------------------------------------------------------ *)

Lemma owned_head : forall A N rest y,
(bv_unsigned A <= y < bv_unsigned A + bv_unsigned N)%Z ->
NoaccessOwned.owned ((A, N) :: rest) y.
Proof. intros A N rest y Hy. exists A, N. split; [left; reflexivity | exact Hy]. Qed.

Lemma lazy_interior_floor : forall A N a n x,
(bv_unsigned A + bv_unsigned N <= 2 ^ 64)%Z ->
In (a, n) (lazy_interior A N) ->
(bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
(bv_unsigned A <= page_round_down_Z x < bv_unsigned A + bv_unsigned N)%Z.
Proof.
intros A N a n x Hfit Hin Hx.
pose proof (word_range A) as RA. pose proof (word_range N) as RN.
unfold lazy_interior in Hin. cbv zeta in Hin.
set (lo := bv_unsigned A) in *. set (hi := (lo + bv_unsigned N)%Z) in *.
set (lo' := (((lo + page_size - 1) / page_size) * page_size)%Z) in *.
set (hi' := ((hi / page_size) * page_size)%Z) in *.
assert (Hlo' : (lo <= lo')%Z).
{ subst lo'. unfold page_size.
  pose proof (Z.div_mod (lo + 4096 - 1) 4096 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (lo + 4096 - 1) 4096 ltac:(lia)) as B. lia. }
assert (Hhi' : (hi' <= hi)%Z).
{ subst hi'. unfold page_size.
  pose proof (Z.div_mod hi 4096 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound hi 4096 ltac:(lia)) as B. lia. }
assert (Hal' : (lo' mod page_size = 0)%Z)
  by (subst lo'; unfold page_size; apply Z.mod_mul; lia).
assert (Hlo0 : (0 <= lo')%Z) by lia.
destruct (Z.ltb_spec lo' hi') as [Hc|Hc]; cbn [In] in Hin; [|destruct Hin].
destruct Hin as [Heq|[]]. injection Heq as <- <-.
rewrite !u64 in Hx by lia.
assert (Hx0 : (0 <= x)%Z) by lia.
pose proof (pfloor_bounds x Hx0) as [B1 B2].
pose proof (pfloor_mono_lo lo' x Hal' Hlo0 ltac:(lia)) as Hge.
subst hi hi'. lia.
Qed.

(* An arm that only ADDS to the mapping ledger, and may add the new
   mapping's interior to the lazy ledger.  Nothing is forgotten. *)
Lemma ledger_add : forall m A N MP,
WF m ->
(bv_unsigned A + bv_unsigned N <= 2 ^ 64)%Z ->
(forall y, (bv_unsigned A <= y < bv_unsigned A + bv_unsigned N)%Z ->
           NoaccessOwned.owned MP y) ->
(forall y, NoaccessOwned.owned (vm_maps (m_vmmaps m)) y -> NoaccessOwned.owned MP y) ->
(forall a n x, In (a, n) (lazy_interior A N ++ m_vm_lazy m) ->
   (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
   NoaccessOwned.owned MP (page_round_down_Z x))
/\ (forall a n x, In (a, n) (m_vm_lazy m) ->
   (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
   NoaccessOwned.owned MP (page_round_down_Z x))
/\ (forall p, In p (m_vm_materialized m) ->
   (bv_unsigned p mod page_size = 0)%Z /\ NoaccessOwned.owned MP (bv_unsigned p)).
Proof.
intros m A N MP HW Hfit Hnew Hkeep.
assert (HOLD : forall a n x, In (a, n) (m_vm_lazy m) ->
          (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
          NoaccessOwned.owned MP (page_round_down_Z x)).
{ intros a n x Hin Hx. apply Hkeep. exact (proj1 (proj2 HW) a n x Hin Hx). }
split; [|split].
- intros a n x Hin Hx. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  + apply Hnew. exact (lazy_interior_floor A N a n x Hfit Hin Hx).
  + exact (HOLD a n x Hin Hx).
- exact HOLD.
- intros p Hin. destruct (proj2 (proj2 HW) p Hin) as [Hpa Hown].
  split; [exact Hpa | exact (Hkeep _ Hown)].
Qed.

(* An arm that REPLACES a page-aligned range: the backing ledgers are
   forgotten over it and the new mapping covers it, so an old owner inside
   the range need not survive. *)
Lemma ledger_repl : forall m A N MP,
WF m ->
(bv_unsigned A mod page_size = 0)%Z ->
((bv_unsigned A + bv_unsigned N) mod page_size = 0)%Z ->
(bv_unsigned A + bv_unsigned N <= 2 ^ 64)%Z ->
(forall y, (bv_unsigned A <= y < bv_unsigned A + bv_unsigned N)%Z ->
           NoaccessOwned.owned MP y) ->
(forall y, NoaccessOwned.owned (vm_maps (m_vmmaps m)) y ->
           ~ (bv_unsigned A <= y < bv_unsigned A + bv_unsigned N)%Z ->
           NoaccessOwned.owned MP y) ->
(forall a n x,
   In (a, n) (lazy_interior A N
              ++ maps_subtract (m_vm_lazy m) (bv_unsigned A)
                   (bv_unsigned A + bv_unsigned N)) ->
   (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
   NoaccessOwned.owned MP (page_round_down_Z x))
/\ (forall a n x,
   In (a, n) (maps_subtract (m_vm_lazy m) (bv_unsigned A)
                (bv_unsigned A + bv_unsigned N)) ->
   (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
   NoaccessOwned.owned MP (page_round_down_Z x))
/\ (forall p, In p (List.filter
       (page_outside_range (bv_unsigned A) (bv_unsigned A + bv_unsigned N))
       (m_vm_materialized m)) ->
   (bv_unsigned p mod page_size = 0)%Z /\ NoaccessOwned.owned MP (bv_unsigned p)).
Proof.
intros m A N MP HW HalA HalE Hfit Hnew Hkeep.
pose proof (word_range A) as RA.
destruct (ledger_forget_sub m MP (bv_unsigned A) (bv_unsigned A + bv_unsigned N)
            HW ltac:(lia) ltac:(pose proof (word_range N); lia) HalA HalE
            ltac:(intros y Hy _ _ Hout; exact (Hkeep y Hy Hout))) as [HLz HMt].
split; [|split; [exact HLz | exact HMt]].
intros a n x Hin Hx. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
- apply Hnew. exact (lazy_interior_floor A N a n x Hfit Hin Hx).
- exact (HLz a n x Hin Hx).
Qed.

(* ------------------------------------------------------------------ *)
(* The three post-state shapes mmap and mremap build, as lemmas about the
   model wrappers, so that no arm has to unfold a setter.  State.v declares
   the accessors and setters [simpl never]; every projection below holds by
   CONVERSION, which is why [reflexivity] closes them where [cbn] cannot. *)
(* ------------------------------------------------------------------ *)

Lemma LZMAT_intro_at : forall (M : Model) (MP : list (word * word)),
vm_maps (m_vmmaps M) = MP ->
(forall a n x, In (a, n) (m_vm_lazy M) ->
   (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
   NoaccessOwned.owned MP (page_round_down_Z x)) ->
(forall p, In p (m_vm_materialized M) ->
   (bv_unsigned p mod page_size = 0)%Z /\ NoaccessOwned.owned MP (bv_unsigned p)) ->
LZ_OWNED M /\ MAT_OWNED M.
Proof.
intros M MP E H1 H2. unfold LZ_OWNED, MAT_OWNED. rewrite E. exact (conj H1 H2).
Qed.

(* ADD: a fresh mapping at the head, nothing forgotten. *)
Lemma ledger_mmap_add : forall m flags A N h',
WF m ->
vm_maps h' = (A, N) :: vm_maps (m_vmmaps m) ->
(bv_unsigned A + bv_unsigned N <= 2 ^ 64)%Z ->
LZ_OWNED (with_mmap_backing flags A N (with_vmmaps h' m))
/\ MAT_OWNED (with_mmap_backing flags A N (with_vmmaps h' m)).
Proof.
intros m flags A N h' HW Hm Hfit.
destruct (ledger_add m A N (vm_maps h') HW Hfit
  ltac:(intros y Hy; rewrite Hm; exact (owned_head A N _ y Hy))
  ltac:(intros y Hy; rewrite Hm; apply NoaccessOwned.owned_cons; exact Hy))
  as (H1 & H2 & H3).
unfold with_mmap_backing. destruct (mmap_noreserve_b flags);
  apply (LZMAT_intro_at _ (vm_maps h'));
  solve [reflexivity | exact H1 | exact H2 | exact H3].
Qed.

(* DESTROY: the range is cut from the mapping ledger and forgotten from both
   backing ledgers, over the SAME page-aligned range. *)
Lemma ledger_mmap_destroyed : forall m A N,
WF m ->
(bv_unsigned A mod page_size = 0)%Z ->
((bv_unsigned A + bv_unsigned N) mod page_size = 0)%Z ->
LZ_OWNED (with_mmap_destroyed A N (mmap_fixed_destroyed_next (m_vmmaps m) A N) m)
/\ MAT_OWNED (with_mmap_destroyed A N (mmap_fixed_destroyed_next (m_vmmaps m) A N) m).
Proof.
intros m A N HW HalA HalE.
pose proof (word_range A) as RA. pose proof (word_range N) as RN.
destruct (ledger_cut_aligned m
            (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned A)
               (bv_unsigned A + bv_unsigned N))
            (bv_unsigned A) (bv_unsigned A + bv_unsigned N)
            HW ltac:(lia) ltac:(lia) HalA HalE
            ltac:(intros y Hy; exact Hy)) as [H1 H2].
apply (LZMAT_intro_at _ (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned A)
          (bv_unsigned A + bv_unsigned N)));
  [reflexivity | exact H1 | exact H2].
Qed.

(* REPLACE, mapping ledger UNCHANGED: the range was already wholly mapped
   ([map_contains]), so the replacement re-protects it without touching
   [vm_maps].  The forget still happens, which only weakens the obligation;
   the new interior is owned because the range was owned to begin with. *)
Lemma ledger_mmap_repl_same : forall m flags A N h',
WF m ->
vm_maps h' = vm_maps (m_vmmaps m) ->
(bv_unsigned A mod page_size = 0)%Z ->
((bv_unsigned A + bv_unsigned N) mod page_size = 0)%Z ->
(bv_unsigned A + bv_unsigned N <= 2 ^ 64)%Z ->
map_contains (vm_maps (m_vmmaps m)) A N = true ->
LZ_OWNED (with_mmap_replacement flags A N (with_vmmaps h' m))
/\ MAT_OWNED (with_mmap_replacement flags A N (with_vmmaps h' m)).
Proof.
intros m flags A N h' HW Hm HalA HalE Hfit Hcont.
pose proof (word_range A) as RA.
destruct (ledger_repl m A N (vm_maps h') HW HalA HalE Hfit
  ltac:(intros y Hy; rewrite Hm;
        exact (NoaccessOwned.map_contains_owned _ A N y Hcont Hy))
  ltac:(intros y Hy _; rewrite Hm; exact Hy)) as (H1 & H2 & H3).
unfold with_mmap_replacement, with_mmap_backing.
destruct (mmap_noreserve_b flags);
  apply (LZMAT_intro_at _ (vm_maps h'));
  solve [reflexivity | exact H1 | exact H2 | exact H3].
Qed.

(* REPLACE over a span: the mapping ledger is cut over the range and the new
   mapping is pushed at the head, which is the shape of
   [mmap_fixed_rw_span_next], [mmap_fixed_noaccess_span_next] and
   [mremap_maps_next]. *)
Lemma ledger_mmap_repl_span : forall m flags A N h',
WF m ->
vm_maps h' = (A, N) :: maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned A)
                          (bv_unsigned A + bv_unsigned N) ->
(bv_unsigned A mod page_size = 0)%Z ->
((bv_unsigned A + bv_unsigned N) mod page_size = 0)%Z ->
(bv_unsigned A + bv_unsigned N <= 2 ^ 64)%Z ->
LZ_OWNED (with_mmap_replacement flags A N (with_vmmaps h' m))
/\ MAT_OWNED (with_mmap_replacement flags A N (with_vmmaps h' m)).
Proof.
intros m flags A N h' HW Hm HalA HalE Hfit.
pose proof (word_range A) as RA.
destruct (ledger_repl m A N (vm_maps h') HW HalA HalE Hfit
  ltac:(intros y Hy; rewrite Hm; exact (owned_head A N _ y Hy))
  ltac:(intros y Hy Hout; rewrite Hm; apply NoaccessOwned.owned_cons;
        apply NoaccessOwned.owned_subtract;
        [exact (WF_maps_fit m HW) | exact Hy | exact Hout]))
  as (H1 & H2 & H3).
unfold with_mmap_replacement, with_mmap_backing.
destruct (mmap_noreserve_b flags);
  apply (LZMAT_intro_at _ (vm_maps h'));
  solve [reflexivity | exact H1 | exact H2 | exact H3].
Qed.

Ltac dif H := match type of H with context [if ?b then _ else _] => destruct b end.
Ltac difn H E := match type of H with context [if ?b then _ else _] => destruct b eqn:E end.
Ltac dei H := match type of H with context [errno_ret_in ?l ?r] => destruct (errno_ret_in l r) end.

(* ------------------------------------------------------------------ *)
(* mmap.  Five post-state shapes and a great many gates; every CheckOk site
   is one of [m], ADD, DESTROY, REPLACE-same or REPLACE-span, and the five
   lemmas above are exactly those.  The ladder below is LPS 6692dfb5's
   [Checks/Sys/Mm/Mmap.v] [check_mmap] walked in its own order. *)
(* ------------------------------------------------------------------ *)

Lemma check_mmap_ledger : forall addr len prot flags fd off eff m m' evs,
check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> WF m ->
LZ_OWNED m' /\ MAT_OWNED m'.
Proof.
intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H HW.
pose proof (proj1 (proj2 HW)) as HL. pose proof (proj2 (proj2 HW)) as HM.
unfold check_mmap in H. cbv zeta in H.
pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
pose proof (word_range len) as Hlenr.
pose proof (word_range addr) as Haddrr.
pose proof (word_range ret) as Hretr.
(* The two argument gates moved between LPS 6692dfb5 and this head: the
   misaligned offset no longer consults [mmap_pglen_ok_b], and the
   non-anonymous arm answers EBADF on an unknown descriptor instead of
   declining outright.  Neither writes a ledger. *)
destruct (negb (mmap_off_aligned_b off)) eqn:Eoff.
{ apply check_ret_only_model in H; subst m'; exact (conj HL HM). }
destruct (negb (mmap_anon_b flags)) eqn:Eanon.
{ destruct (fd_lookup (m_fds m) (fd32 fd)) as [e|] eqn:Efd; [discriminate|].
  apply check_ret_only_model in H; subst m'; exact (conj HL HM). }
destruct (w_is0 len) eqn:Elen.
{ destruct (mmap_plain_anon_b flags); [|discriminate].
  apply check_ret_only_model in H; subst m'; exact (conj HL HM). }
pose proof (w_is0_false len Elen) as Hlen0.
assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z)
  by (apply page_round_up_pos; lia).
assert (HnM : (page_round_up_Z (bv_unsigned len) mod page_size = 0)%Z)
  by apply pup_mod.
destruct (mmap_modeled_b prot flags off) eqn:Emod.
{ destruct ws, us, cs, ci; try discriminate.
  dei H.
  { destruct zs; [|discriminate]. injection H as <- <-. exact (conj HL HM). }
  difn H E; [|discriminate]. injection H as <- <-.
  (* LPS revision/place: the two FREELY PLACED arms no longer gate on a
     chain of boolean tests.  [Placement.linux_place_is] is one predicate,
     and [linux_place_is_admissible] returns the same four facts the chain
     used to yield -- alignment, positivity, the [alloc_top] bound and
     [region_free] -- so only the peeling changes, not the argument.  The
     MAP_FIXED arms below are unchanged: they place at [addr], so no search
     runs and no placement predicate appears. *)
  apply andb_true_iff in E as [E Hzs].
  apply andb_true_iff in E as [Hplace Hbud].
  pose proof (Placement.linux_place_is_admissible _ _ _ _ _ HnZ HnM Hplace)
    as (Halign & Hpos & Hceil & Hfree).
  apply ledger_mmap_add; [exact HW | reflexivity | rewrite u64 by lia; lia]. }
destruct (mmap_noaccess_b prot flags off) eqn:Enoa.
{ destruct ws, zs, cs, ci; try discriminate.
  dei H.
  { destruct us; [|discriminate]. injection H as <- <-. exact (conj HL HM). }
  difn H E; [|discriminate]. injection H as <- <-.
  apply andb_true_iff in E as [Hplace Hus].
  pose proof (Placement.linux_place_is_admissible _ _ _ _ _ HnZ HnM Hplace)
    as (Halign & Hpos & Hceil & Hfree).
  apply ledger_mmap_add; [exact HW | reflexivity | rewrite u64 by lia; lia]. }
(* From here every arm is MAP_FIXED-shaped: the same four argument gates,
   so [addr] is page aligned and [addr + nZ] is below [alloc_top]. *)
destruct (mmap_fixed_noaccess_b prot flags off) eqn:Efix.
{ difn H Enomem; [apply check_ret_only_model in H; subst m'; exact (conj HL HM)|].
  difn H Eceil; [discriminate|].
  difn H Ealign; [apply check_ret_only_model in H; subst m'; exact (conj HL HM)|].
  difn H Epos; [discriminate|].
  apply negb_false_iff, Z.leb_le in Eceil.
  apply negb_false_iff, Z.eqb_eq in Ealign.
  assert (HU : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
               = page_round_up_Z (bv_unsigned len)) by (apply u64; lia).
  assert (HAE : ((bv_unsigned addr
                  + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
                 mod page_size = 0)%Z)
    by (rewrite HU; apply NoaccessOwned.aligned_add; [exact Ealign | exact HnM]).
  difn H Elive.
  - destruct ws, zs, cs, ci; try discriminate.
    difn H Eerr.
    + destruct us as [|u us]; [injection H as <- <-; exact (conj HL HM)|].
      difn H Edest; [|discriminate]. injection H as <- <-.
      apply ledger_mmap_destroyed; [exact HW | exact Ealign | exact HAE].
    + difn H Eok; [|discriminate]. injection H as <- <-.
      apply andb_true_iff in Elive as [_ Hcont].
      apply ledger_mmap_repl_same;
        [exact HW | reflexivity | exact Ealign | exact HAE
        | rewrite HU; lia | exact Hcont].
  - difn H Efree.
    + destruct ws, zs, cs, ci; try discriminate.
      dei H.
      * destruct us; [|discriminate]. injection H as <- <-. exact (conj HL HM).
      * difn H Eok; [|discriminate]. injection H as <- <-.
        apply ledger_mmap_add; [exact HW | reflexivity | rewrite HU; lia].
    + difn H Espan; [|discriminate].
      destruct ws, zs, cs, ci; try discriminate.
      difn H Eerr.
      * destruct us as [|u us]; [injection H as <- <-; exact (conj HL HM)|].
        difn H Edest; [|discriminate]. injection H as <- <-.
        apply ledger_mmap_destroyed; [exact HW | exact Ealign | exact HAE].
      * difn H Eok; [|discriminate]. injection H as <- <-.
        apply ledger_mmap_repl_span;
          [exact HW | reflexivity | exact Ealign | exact HAE | rewrite HU; lia]. }
destruct (mmap_fixed_rw_b prot flags off) eqn:Efixrw.
2: {
  destruct (mmap_noreplace_noaccess_b prot flags off) eqn:Enrn.
  { difn H Enomem; [apply check_ret_only_model in H; subst m'; exact (conj HL HM)|].
    difn H Eceil; [discriminate|].
    difn H Ealign; [apply check_ret_only_model in H; subst m'; exact (conj HL HM)|].
    difn H Epos; [discriminate|].
    apply negb_false_iff, Z.leb_le in Eceil.
    assert (HU : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                 = page_round_up_Z (bv_unsigned len)) by (apply u64; lia).
    difn H Efree.
    - destruct ws, zs, cs, ci; try discriminate.
      dei H.
      + destruct us; [|discriminate]. injection H as <- <-. exact (conj HL HM).
      + difn H Eok; [|discriminate]. injection H as <- <-.
        apply ledger_mmap_add; [exact HW | reflexivity | rewrite HU; lia].
    - destruct ws, zs, us, cs, ci; try discriminate.
      difn H Eerr; [|discriminate]. injection H as <- <-. exact (conj HL HM). }
  destruct (mmap_noreplace_rw_b prot flags off) eqn:Enrr; [|discriminate].
  difn H Enomem; [apply check_ret_only_model in H; subst m'; exact (conj HL HM)|].
  difn H Eceil; [discriminate|].
  difn H Ealign; [apply check_ret_only_model in H; subst m'; exact (conj HL HM)|].
  difn H Epos; [discriminate|].
  apply negb_false_iff, Z.leb_le in Eceil.
  assert (HU : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
               = page_round_up_Z (bv_unsigned len)) by (apply u64; lia).
  difn H Efree.
  - destruct ws, us, cs, ci; try discriminate.
    dei H.
    + destruct zs; [|discriminate]. injection H as <- <-. exact (conj HL HM).
    + difn H Eok; [|discriminate]. injection H as <- <-.
      apply ledger_mmap_add; [exact HW | reflexivity | rewrite HU; lia].
  - destruct ws, zs, us, cs, ci; try discriminate.
    difn H Eerr; [|discriminate]. injection H as <- <-. exact (conj HL HM). }
difn H Enomem; [apply check_ret_only_model in H; subst m'; exact (conj HL HM)|].
difn H Eceil; [discriminate|].
difn H Ealign; [apply check_ret_only_model in H; subst m'; exact (conj HL HM)|].
difn H Epos; [discriminate|].
apply negb_false_iff, Z.leb_le in Eceil.
apply negb_false_iff, Z.eqb_eq in Ealign.
assert (HU : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
             = page_round_up_Z (bv_unsigned len)) by (apply u64; lia).
assert (HAE : ((bv_unsigned addr
                + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
               mod page_size = 0)%Z)
  by (rewrite HU; apply NoaccessOwned.aligned_add; [exact Ealign | exact HnM]).
difn H Elive.
- destruct ws, cs, ci; try discriminate.
  difn H Eerr.
  + destruct zs; [|discriminate].
    destruct us as [|u us]; [injection H as <- <-; exact (conj HL HM)|].
    difn H Edest; [|discriminate]. injection H as <- <-.
    apply ledger_mmap_destroyed; [exact HW | exact Ealign | exact HAE].
  + destruct us; [|discriminate].
    difn H Eok; [|discriminate]. injection H as <- <-.
    apply andb_true_iff in Elive as [_ Hcont].
    apply ledger_mmap_repl_same;
      [exact HW | reflexivity | exact Ealign | exact HAE
      | rewrite HU; lia | exact Hcont].
- difn H Efree.
  + destruct ws, us, cs, ci; try discriminate.
    dei H.
    * destruct zs; [|discriminate]. injection H as <- <-. exact (conj HL HM).
    * difn H Eok; [|discriminate]. injection H as <- <-.
      apply ledger_mmap_add; [exact HW | reflexivity | rewrite HU; lia].
  + difn H Espan; [|discriminate].
    destruct ws, cs, ci; try discriminate.
    difn H Eerr.
    * destruct zs; [|discriminate].
      destruct us as [|u us]; [injection H as <- <-; exact (conj HL HM)|].
      difn H Edest; [|discriminate]. injection H as <- <-.
      apply ledger_mmap_destroyed; [exact HW | exact Ealign | exact HAE].
    * destruct us; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      apply ledger_mmap_repl_span;
        [exact HW | reflexivity | exact Ealign | exact HAE | rewrite HU; lia].
Qed.

Lemma check_mmap_WF : forall addr len prot flags fd off eff m m' evs,
check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> WF m -> WF m'.
Proof.
intros addr len prot flags fd off eff m m' evs H HW.
destruct (check_mmap_ledger _ _ _ _ _ _ _ _ _ _ H HW) as [HL HM].
destruct (proj1 HW) as (Hwf & Hfit & Hna).
split; [|exact (conj HL HM)].
split; [exact (check_mmap_preserves _ _ _ _ _ _ _ _ _ _ H Hwf)|].
split; [exact (MapsFit.check_mmap_preserves_fit _ _ _ _ _ _ _ _ _ _ H Hfit)|].
exact (NoaccessOwned.check_mmap_preserves_na _ _ _ _ _ _ _ _ _ _ H Hwf Hfit Hna).
Qed.

(* ------------------------------------------------------------------ *)
(* mremap.  The only arm that MOVES backing rather than only adding or
   forgetting it: [State.vm_resize_backing] cuts the lazy ledger over the
   source range and then over the destination range, keeps the materialized
   pages outside both, and re-bases the source's pages onto the
   destination.  [Mremap.mremap_maps_next] cuts the mapping ledger over the
   SOURCE range and pushes the destination at the head, so the two sides
   are cut over DIFFERENT ranges -- which is why this arm needs its own
   lemma rather than [ledger_repl]. *)
(* ------------------------------------------------------------------ *)

Lemma aligned_move : forall a b c,
(a mod page_size = 0)%Z -> (b mod page_size = 0)%Z -> (c mod page_size = 0)%Z ->
((a + (b - c)) mod page_size = 0)%Z.
Proof.
intros a b c Ha Hb Hc. unfold page_size in *.
destruct (Z.mod_divide a 4096 ltac:(lia)) as [Da _]. destruct (Da Ha) as [x Hx].
destruct (Z.mod_divide b 4096 ltac:(lia)) as [Db _]. destruct (Db Hb) as [y Hy].
destruct (Z.mod_divide c 4096 ltac:(lia)) as [Dc _]. destruct (Dc Hc) as [z Hz].
subst. replace (x * 4096 + (y * 4096 - z * 4096))%Z with ((x + y - z) * 4096)%Z by lia.
apply Z.mod_mul. lia.
Qed.

(* [page_size] is a Definition, so [_ mod page_size] is nonlinear to lia and a
   context carrying several alignment hypotheses makes its preprocessing
   explode.  Every numeric goal below is a plain range fact, so drop them. *)
Ltac zlia := repeat match goal with
                    | [ H : (_ mod page_size = 0)%Z |- _ ] => clear H
                    end; lia.
Lemma ledger_mremap : forall m sl old old_n dst new_n,
WF m ->
(bv_unsigned old mod page_size = 0)%Z ->
(bv_unsigned old_n mod page_size = 0)%Z ->
(bv_unsigned dst mod page_size = 0)%Z ->
(bv_unsigned new_n mod page_size = 0)%Z ->
(bv_unsigned dst + bv_unsigned new_n <= 2 ^ 64)%Z ->
LZ_OWNED (vm_resize_backing sl old old_n dst new_n
            (with_vmmaps (mremap_maps_next (m_vmmaps m) old old_n dst new_n) m))
/\ MAT_OWNED (vm_resize_backing sl old old_n dst new_n
            (with_vmmaps (mremap_maps_next (m_vmmaps m) old old_n dst new_n) m)).
Proof.
intros m sl old old_n dst new_n HW HalO HalON HalD HalNN Hfit.
pose proof (word_range old) as RO. pose proof (word_range old_n) as RON.
pose proof (word_range dst) as RD. pose proof (word_range new_n) as RNN.
set (olo := bv_unsigned old) in *. set (ohi := (olo + bv_unsigned old_n)%Z) in *.
set (dlo := bv_unsigned dst) in *. set (dhi := (dlo + bv_unsigned new_n)%Z) in *.
assert (HalOH : (ohi mod page_size = 0)%Z)
  by (subst ohi; apply NoaccessOwned.aligned_add; assumption).
assert (HalDH : (dhi mod page_size = 0)%Z)
  by (subst dhi; apply NoaccessOwned.aligned_add; assumption).
set (MP := ((dst, new_n) :: maps_subtract (vm_maps (m_vmmaps m)) olo ohi)).
assert (HMP : vm_maps (mremap_maps_next (m_vmmaps m) old old_n dst new_n) = MP)
  by reflexivity.
(* an old owner outside the SOURCE range survives the cut and the cons *)
assert (TR : forall y, NoaccessOwned.owned (vm_maps (m_vmmaps m)) y ->
             ~ (olo <= y < ohi)%Z -> NoaccessOwned.owned MP y).
{ intros y Hy Hout. apply NoaccessOwned.owned_cons.
  apply NoaccessOwned.owned_subtract;
    [exact (WF_maps_fit m HW) | exact Hy | exact Hout]. }
(* every byte of the DESTINATION range is owned by the new head *)
assert (NEW : forall y, (dlo <= y < dhi)%Z -> NoaccessOwned.owned MP y).
{ intros y Hy. exact (owned_head dst new_n _ y Hy). }
assert (HLZF : MapsFit.maps_fit (m_vm_lazy m)) by exact (WF_lazy_fit m HW).
(* the lazy ledger after BOTH cuts *)
assert (KEEPL : forall a n x,
  In (a, n) (maps_subtract (maps_subtract (m_vm_lazy m) olo ohi) dlo dhi) ->
  (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
  NoaccessOwned.owned MP (page_round_down_Z x)).
{ intros a n x Hin Hx.
  assert (H0 : (0 <= x)%Z) by (pose proof (word_range a); zlia).
  destruct (owned_subtract_inv _ dlo dhi x ltac:(zlia) ltac:(zlia)
              (MapsFit.maps_subtract_fit _ _ _ HLZF)
              (ex_intro _ a (ex_intro _ n (conj Hin Hx)))) as [Ho1 _].
  destruct (owned_subtract_inv _ olo ohi x ltac:(zlia) ltac:(zlia) HLZF Ho1)
    as [Ho2 Hout].
  destruct Ho2 as (a0 & n0 & Hin0 & Hx0).
  pose proof (proj1 (proj2 HW) a0 n0 x Hin0 Hx0) as Hown.
  apply TR; [exact Hown|].
  intros Hc. apply Hout.
  exact (byte_in_aligned_range olo ohi x HalO HalOH ltac:(zlia) H0 Hc). }
set (KL := maps_subtract (maps_subtract (m_vm_lazy m) olo ohi) dlo dhi) in *.
set (KP := List.filter (page_outside_range dlo dhi)
             (List.filter (page_outside_range olo ohi) (m_vm_materialized m))) in *.
assert (EMT : m_vm_materialized (vm_resize_backing sl old old_n dst new_n
                (with_vmmaps (mremap_maps_next (m_vmmaps m) old old_n dst new_n) m))
              = (if sl then List.map (move_page_base old dst)
                         (List.filter
                           (fun p => page_in_half_open olo ohi p
                                     && (bv_unsigned p - olo <? bv_unsigned new_n)%Z)
                           (m_vm_materialized m))
                 else []) ++ KP)
  by (destruct sl; reflexivity).
assert (ELZ : m_vm_lazy (vm_resize_backing sl old old_n dst new_n
                (with_vmmaps (mremap_maps_next (m_vmmaps m) old old_n dst new_n) m))
              = (if sl then lazy_interior dst new_n ++ KL else KL))
  by (destruct sl; reflexivity).
apply (LZMAT_intro_at _ MP); [exact HMP | |].
- intros a n x Hin Hx. rewrite ELZ in Hin.
  assert (HKL : In (a, n) KL -> NoaccessOwned.owned MP (page_round_down_Z x))
    by (intros HK; exact (KEEPL a n x HK Hx)).
  destruct sl; [|exact (HKL Hin)].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  + apply NEW. exact (lazy_interior_floor dst new_n a n x ltac:(zlia) Hin Hx).
  + exact (HKL Hin).
- intros p Hin. rewrite EMT in Hin.
  assert (HKP : In p KP ->
            (bv_unsigned p mod page_size = 0)%Z
            /\ NoaccessOwned.owned MP (bv_unsigned p)).
  { intros HK. subst KP.
    apply List.filter_In in HK as [HK Hod].
    apply List.filter_In in HK as [HK Hoo].
    destruct (proj2 (proj2 HW) p HK) as [Hpa Hown].
    pose proof (word_range p) as RP.
    split; [exact Hpa|]. apply TR; [exact Hown|].
    unfold page_outside_range in Hoo. apply negb_true_iff in Hoo.
    apply andb_false_iff in Hoo.
    intros [H1 H2]. destruct Hoo as [E|E];
      [apply Z.leb_nle in E | apply Z.ltb_nlt in E]; zlia. }
  apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [|exact (HKP Hin)].
  destruct sl; [|destruct Hin].
  (* a page re-based onto the destination *)
    apply in_map_iff in Hin as (q & Hq & Hinq).
    apply List.filter_In in Hinq as [Hinq Hsel].
    apply andb_true_iff in Hsel as [Hin2 Hoff].
    unfold page_in_half_open in Hin2. apply andb_true_iff in Hin2 as [Hge Hlt].
    apply Z.leb_le in Hge. apply Z.ltb_lt in Hlt. apply Z.ltb_lt in Hoff.
    destruct (proj2 (proj2 HW) q Hinq) as [Hqa _].
    pose proof (word_range q) as RQ.
    assert (HV : bv_unsigned p = (dlo + (bv_unsigned q - olo))%Z).
    { subst p. unfold move_page_base. apply u64. zlia. }
  split.
  + rewrite HV. apply aligned_move; assumption.
  + apply NEW. rewrite HV. zlia.
Qed.

Lemma check_mremap_ledger : forall old old_size new_size flags eff m m' evs,
check_mremap old old_size new_size flags eff m = CheckOk m' evs -> WF m ->
LZ_OWNED m' /\ MAT_OWNED m'.
Proof.
intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H HW.
pose proof (proj1 (proj2 HW)) as HL. pose proof (proj2 (proj2 HW)) as HM.
unfold check_mremap in H. cbv zeta in H.
pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
pose proof (word_range old) as Hor.
pose proof (word_range old_size) as Hos.
pose proof (word_range new_size) as Hns.
pose proof (word_range ret) as Hrr.
difn H Eflag; [discriminate|].
difn H Ealign; [apply check_ret_only_model in H; subst m'; exact (conj HL HM)|].
difn H Enew; [apply check_ret_only_model in H; subst m'; exact (conj HL HM)|].
difn H Etask; [apply check_ret_only_model in H; subst m'; exact (conj HL HM)|].
difn H Eold; [discriminate|].
difn H Esrc; [discriminate|].
difn H Eeq; [apply check_ret_only_model in H; subst m'; exact (conj HL HM)|].
destruct ws; [|discriminate]. destruct ci; [|discriminate].
apply negb_false_iff, Z.eqb_eq in Ealign.
apply Z.ltb_ge in Etask.
assert (Htask : (TASK_SIZE < 2 ^ 64)%Z) by (unfold TASK_SIZE; zlia).
(* the source gate bounds the OLD size; the TASK_SIZE gate bounds the NEW one *)
apply negb_false_iff in Esrc. apply andb_true_iff in Esrc as [Esrc Huni].
pose proof Esrc as Esrc'. unfold mremap_source_b in Esrc'.
apply andb_true_iff in Esrc' as [Esrc' _]. apply andb_true_iff in Esrc' as [Esrc' _].
apply andb_true_iff in Esrc' as [Hoceil _]. apply Z.leb_le in Hoceil.
assert (HoldZ : (0 <= page_round_up_Z (bv_unsigned old_size))%Z)
  by (apply page_round_up_Z_nonneg; zlia).
assert (HnewZ : (0 <= page_round_up_Z (bv_unsigned new_size))%Z)
  by (apply page_round_up_Z_nonneg; zlia).
assert (HUO : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
              = page_round_up_Z (bv_unsigned old_size)) by (apply u64; zlia).
assert (HUN : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
              = page_round_up_Z (bv_unsigned new_size))
  by (apply u64; unfold TASK_SIZE in *; zlia).
assert (HAO : (bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
               mod page_size = 0)%Z) by (rewrite HUO; apply pup_mod).
assert (HAN : (bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
               mod page_size = 0)%Z) by (rewrite HUN; apply pup_mod).
destruct (errno_ret_in mremap_errnos ret) eqn:Eerr.
{ destruct zs, us, cs; try discriminate. injection H as <- <-. exact (conj HL HM). }
destruct (bv_eqb ret old) eqn:Eret.
- (* shrink and in-place grow: the destination IS the source base *)
  difn H Eshrink.
  + difn H Eok; [|discriminate]. injection H as <- <-.
    apply Z.ltb_lt in Eshrink.
    apply ledger_mremap;
      [exact HW | exact Ealign | exact HAO | exact Ealign | exact HAN
      | rewrite HUN; zlia].
  + difn H Egrow; [|discriminate].
    difn H Eok; [|discriminate]. injection H as <- <-.
    unfold mremap_inplace_grow_b in Egrow. cbv zeta in Egrow.
    apply andb_true_iff in Egrow as [Egrow _].
    apply andb_true_iff in Egrow as [Hgceil _].
    apply Z.leb_le in Hgceil.
    apply ledger_mremap;
      [exact HW | exact Ealign | exact HAO | exact Ealign | exact HAN
      | rewrite HUN; zlia].
- (* the move: the destination is the returned base, gated by mremap_fresh_b *)
  difn H Emove; [|discriminate]. injection H as <- <-.
  apply andb_true_iff in Emove as [Emove _].
  apply andb_true_iff in Emove as [Emove _].
  apply andb_true_iff in Emove as [Emove _].
  apply andb_true_iff in Emove as [_ Hfresh].
  unfold mremap_fresh_b in Hfresh. cbv zeta in Hfresh.
  apply andb_true_iff in Hfresh as [Hfresh _].
  apply andb_true_iff in Hfresh as [Hfresh Hffree].
  apply andb_true_iff in Hfresh as [Hfresh Hfceil].
  apply andb_true_iff in Hfresh as [Hfresh _].
  apply andb_true_iff in Hfresh as [_ Hfalign].
  apply Z.leb_le in Hfceil. apply Z.eqb_eq in Hfalign.
  apply ledger_mremap;
    [exact HW | exact Ealign | exact HAO | exact Hfalign | exact HAN
    | rewrite HUN; zlia].
Qed.

Lemma check_mremap_WF : forall old old_size new_size flags eff m m' evs,
check_mremap old old_size new_size flags eff m = CheckOk m' evs -> WF m -> WF m'.
Proof.
intros old old_size new_size flags eff m m' evs H HW.
destruct (check_mremap_ledger _ _ _ _ _ _ _ _ H HW) as [HL HM].
destruct (proj1 HW) as (Hwf & Hfit & Hna).
split; [|exact (conj HL HM)].
split; [exact (check_mremap_preserves _ _ _ _ _ _ _ _ H Hwf)|].
split; [exact (MapsFit.check_mremap_preserves_fit _ _ _ _ _ _ _ _ H Hfit)|].
exact (NoaccessOwned.check_mremap_preserves_na _ _ _ _ _ _ _ _ H Hwf Hfit Hna).
Qed.

(* ==================================================================== *)
(* DISCHARGING THE BUDGET PREMISE'S LEDGER HYPOTHESES.

   [Checks/BudgetPremise] used to carry a variant of
   [mremap_move_budget_admits_fresh] assuming [m_vm_lazy m = []] and
   [m_vm_materialized m = []], with a corollary file above it restating
   that assumption.  Neither emptiness is a run invariant -- it fails from
   a run's first successful MAP_NORESERVE reservation on -- so neither was
   usable on a state a run actually reaches.  Removing that assumption is
   what this file exists for, and the two dead lemmas and the corollary
   file were deleted in the same commit that added the replacement below:
   they had no consumer in the model and none in the proof forks either.

   What the two emptiness hypotheses are really standing in for is visible
   in [mremap_move_budget_admits_fresh]'s own statement: two SYNTACTIC list
   identities saying that cutting the DESTINATION range out of the already
   source-cut ledgers changes nothing.  Both say "the destination range
   holds no backing", and that is exactly what [WF] gives beside the
   lemma's own [region_free]: a lazy byte or a materialized page there
   would be owned in [vm_maps], which [region_free] forbids.

   [WF] also supplies two of the remaining hypotheses -- [noaccess_pages_owned]
   from [sys_inv]'s [na_inv], and the fit of the live mappings from
   [vm_fit] -- so FOUR hypotheses go, not two.

   ONE FACT [WF] DOES NOT STATE AND THIS NEEDS.  The identities are
   syntactic, and [State.iv_subtract a sz lo hi] with [sz = 0] and
   [lo <= a < hi] returns [[] ++ []]: it DROPS a zero-size entry.  So the
   equality needs every lazy entry to be nonzero.  That is true and
   inductive -- [init_model]'s ledger is [[]], [lazy_interior] yields an
   empty list or one nonzero entry, and a cut of a nonzero entry is
   nonzero -- but it does not follow from [WF] as merged.  It is carried
   here as [LZ_NZ], a separate invariant, rather than as a fourth conjunct
   of [WF], so that no statement already merged and already consumed by
   other lanes changes under them. *)
(* ==================================================================== *)

Definition LZ_NZ (m : Model) : Prop :=
forall a n, In (a, n) (m_vm_lazy m) -> (0 < bv_unsigned n)%Z.

(* A region the ledger leaves free owns nothing. *)
Lemma region_free_excludes : forall h dst n y,
region_free (vm_reserved h ++ vm_maps h) dst n = true ->
NoaccessOwned.owned (vm_maps h) y ->
~ (bv_unsigned dst <= y < bv_unsigned dst + bv_unsigned n)%Z.
Proof.
intros h dst n y Hfree Hown Hin.
assert (Howns : owns_b (dst, n) y = true) by (apply owns_intro; lia).
pose proof (region_free_no_owner _ _ _ _ Hfree Howns) as Hz.
destruct Hown as (b & s & Hinb & Hyb).
pose proof (owners_ge1 (vm_reserved h ++ vm_maps h) (b, s) y
              (in_or_app _ _ _ (or_intror Hinb))
              (owns_intro b s y (proj1 Hyb) (proj2 Hyb))) as Hge.
lia.
Qed.

(* A cut over a range the list avoids is the identity.  The nonzero
   hypothesis is the zero-size entry above, and it is why [LZ_NZ] exists. *)
Lemma maps_subtract_noop : forall L lo hi,
(lo <= hi)%Z ->
(forall a n, In (a, n) L ->
   (0 < bv_unsigned n)%Z
   /\ ((bv_unsigned a + bv_unsigned n <= lo)%Z \/ (hi <= bv_unsigned a)%Z)) ->
maps_subtract L lo hi = L.
Proof.
induction L as [|[a sz] r IH]; intros lo hi Hlh H; [reflexivity|].
cbn [maps_subtract].
destruct (H a sz (or_introl eq_refl)) as [Hnz Hout].
pose proof (word_range a) as Ra. pose proof (word_range sz) as Rs.
assert (Hiv : iv_subtract a sz lo hi = [(a, sz)]).
{ unfold iv_subtract. cbv zeta. destruct Hout as [Hlow|Hhigh].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [_|Hc]; [|lia].
    destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Hc2|_]; [lia|].
    cbn [app]. do 2 f_equal.
    apply bv_eq. rewrite u64 by lia. lia.
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [Hc|_]; [lia|].
    destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [_|Hc2]; [|lia].
    cbn [app]. f_equal. f_equal.
    + apply bv_eq. rewrite u64 by lia. lia.
    + apply bv_eq. rewrite u64 by lia. lia. }
rewrite Hiv. cbn [app]. f_equal.
apply IH; [exact Hlh|]. intros b m Hin. exact (H b m (or_intror Hin)).
Qed.

(* Every entry a cut leaves is a sub-interval of an entry that was there,
   and it is nonzero when the originals are.  The fit hypothesis is what
   keeps the right-hand remnant's [Z_to_bv] lossless. *)
Lemma maps_subtract_entry_inv : forall L lo hi a n,
MapsFit.maps_fit L ->
(forall b m, In (b, m) L -> (0 < bv_unsigned m)%Z) ->
In (a, n) (maps_subtract L lo hi) ->
(0 < bv_unsigned n)%Z
/\ exists a0 n0, In (a0, n0) L
   /\ forall x, (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
                (bv_unsigned a0 <= x < bv_unsigned a0 + bv_unsigned n0)%Z.
Proof.
induction L as [|[b sz] r IH]; intros lo hi a n Hfit Hnz Hin; [destruct Hin|].
cbn [maps_subtract] in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
- pose proof (word_range b) as Rb. pose proof (word_range sz) as Rs.
  pose proof (Hnz b sz (or_introl eq_refl)) as Hbz.
  assert (Hbf : (bv_unsigned b + bv_unsigned sz <= 2 ^ 64)%Z).
  { pose proof (Hfit b sz (or_introl eq_refl)) as Hb.
    unfold two_pow_64 in Hb. exact Hb. }
  unfold iv_subtract in Hin. cbv zeta in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  + destruct (Z.ltb_spec (bv_unsigned b) lo) as [Hc|Hc]; cbn [In] in Hin;
      [|destruct Hin].
    destruct Hin as [Heq|[]]. injection Heq as <- <-.
    rewrite u64 by lia. split; [lia|].
    exists b, sz. split; [left; reflexivity | intros x Hx; lia].
  + destruct (Z.ltb_spec hi (bv_unsigned b + bv_unsigned sz)) as [Hc|Hc];
      cbn [In] in Hin; [|destruct Hin].
    destruct Hin as [Heq|[]]. injection Heq as <- <-.
    rewrite !u64 by lia. split; [lia|].
    exists b, sz. split; [left; reflexivity | intros x Hx; lia].
- destruct (IH lo hi a n
             (fun c u Hcu => Hfit c u (or_intror Hcu))
             (fun c u Hcu => Hnz c u (or_intror Hcu)) Hin)
    as (Hnz0 & a0 & n0 & Hin0 & Hsub).
  split; [exact Hnz0|]. exists a0, n0. split; [right; exact Hin0 | exact Hsub].
Qed.

(* The same for the materialized ledger, where the cut is a filter. *)
Lemma filter_outside_noop : forall lo hi (P : list word),
(forall p, In p P -> page_outside_range lo hi p = true) ->
List.filter (page_outside_range lo hi) P = P.
Proof.
induction P as [|p r IH]; intros H; [reflexivity|].
cbn [List.filter]. rewrite (H p (or_introl eq_refl)). f_equal.
apply IH. intros q Hin. exact (H q (or_intror Hin)).
Qed.


(* THE REPLACEMENT for the deleted emptiness variant.  Same conclusion as
   [BudgetPremise.mremap_move_budget_admits_fresh], with the two
   hypotheses [WF] already carries -- [noaccess_pages_owned] and the fit
   of the live mappings -- supplied from [WF] itself, and the two
   lazy-ledger identities proved rather than assumed.  So a caller on a
   reachable state can use this one, which was the whole point. *)
Lemma mremap_move_budget_admits_fresh_wf : forall m old old_n dst new_n,
WF m -> LZ_NZ m ->
(bv_unsigned dst mod page_size = 0)%Z ->
(bv_unsigned new_n mod page_size = 0)%Z ->
(0 < bv_unsigned new_n)%Z ->
(bv_unsigned dst + bv_unsigned new_n <= alloc_top (m_vmmaps m))%Z ->
region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) dst new_n = true ->
Mremap.mremap_move_budget_b m old old_n new_n = true ->
Mremap.mremap_final_budget_b m old old_n dst new_n = true.
Proof.
intros m old old_n dst new_n HW HNZ Hdalign Hnmod Hpos Hdtop Hdfree Hmv.
pose proof (word_range dst) as Rd. pose proof (word_range new_n) as Rn.
set (dlo := bv_unsigned dst) in *.
set (dhi := (dlo + bv_unsigned new_n)%Z) in *.
assert (HalD : (dlo mod page_size = 0)%Z) by exact Hdalign.
assert (HalDH : (dhi mod page_size = 0)%Z)
  by (subst dhi; apply NoaccessOwned.aligned_add; assumption).
(* no owner of the live ledger lies in the destination range *)
assert (NOOWN : forall y, NoaccessOwned.owned (vm_maps (m_vmmaps m)) y ->
                ~ (dlo <= y < dhi)%Z)
  by (intros y Hy; exact (region_free_excludes _ _ _ y Hdfree Hy)).
(* hence no lazy byte and no materialized page lies there *)
assert (NOLZ : forall a n x, In (a, n) (m_vm_lazy m) ->
          (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
          ~ (dlo <= x < dhi)%Z).
{ intros a n x Hin Hx Hc.
  assert (H0 : (0 <= x)%Z) by (pose proof (word_range a); lia).
  pose proof (proj1 (proj2 HW) a n x Hin Hx) as Hown.
  apply (NOOWN _ Hown).
  pose proof (pfloor_bounds x H0) as [B1 B2].
  split; [exact (pfloor_mono_lo dlo x HalD ltac:(lia) ltac:(lia))|].
  pose proof (aligned_lt_step _ _ (pfloor_mod x) HalDH) as Hs. lia. }
apply (BudgetPremise.mremap_move_budget_admits_fresh m old old_n dst new_n
         Hdalign Hnmod Hpos Hdtop Hdfree
         (NoaccessOwned.sys_inv_noaccess_pages_owned _ (proj1 HW))
         (proj1 (proj2 (proj1 HW)))).
- (* the lazy identity *)
  apply maps_subtract_noop; [subst dhi; lia|]. intros a n Hin.
  destruct (maps_subtract_entry_inv _ _ _ _ _ (WF_lazy_fit m HW) HNZ Hin)
    as (Hnz0 & a0 & n0 & Hin0 & Hsub).
  split; [exact Hnz0|].
  destruct (Z.le_gt_cases (bv_unsigned a + bv_unsigned n) dlo) as [Hl|Hl];
    [left; exact Hl|].
  destruct (Z.le_gt_cases dhi (bv_unsigned a)) as [Hr|Hr]; [right; exact Hr|].
  exfalso.
  set (x := Z.max (bv_unsigned a) dlo).
  assert (Hxe : (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z)
    by (subst x; pose proof (word_range a); lia).
  assert (Hxd : (dlo <= x < dhi)%Z) by (subst x; lia).
  exact (NOLZ a0 n0 x Hin0 (Hsub x Hxe) Hxd).
- (* the materialized identity *)
  apply filter_outside_noop. intros p Hin.
  apply List.filter_In in Hin as [Hin _].
  destruct (proj2 (proj2 HW) p Hin) as [Hpa Hown].
  pose proof (NOOWN _ Hown) as Hout.
  unfold page_outside_range. apply negb_true_iff. apply andb_false_iff.
  destruct (Z.leb_spec dlo (bv_unsigned p)) as [H1|H1]; [|left; apply Z.leb_nle; lia].
  destruct (Z.ltb_spec (bv_unsigned p) dhi) as [H2|H2]; [|right; apply Z.ltb_nlt; lia].
  exfalso. exact (Hout (conj H1 H2)).
- exact Hmv.
Qed.

(* ==================================================================== *)
(* [LZ_NZ]'s TWO BUILDING BLOCKS.

   Every post-state lazy ledger in the model is built from exactly two
   things: [State.lazy_interior], which mmap and mremap push for a fresh
   MAP_NORESERVE mapping, and [State.maps_subtract], which every forget
   applies.  So [LZ_NZ]'s arms all reduce to these two lemmas, and the
   per-arm ladders are bookkeeping on top of them. *)
(* ==================================================================== *)

(* The interior is the PAGE-ALIGNED inside of a mapping, so when it is
   present at all it is a single entry of at least one page. *)
Lemma lazy_interior_nz : forall A N a n,
(bv_unsigned A + bv_unsigned N <= 2 ^ 64)%Z ->
In (a, n) (lazy_interior A N) -> (0 < bv_unsigned n)%Z.
Proof.
intros A N a n Hfit Hin.
pose proof (word_range A) as RA. pose proof (word_range N) as RN.
unfold lazy_interior in Hin. cbv zeta in Hin.
set (lo := bv_unsigned A) in *. set (hi := (lo + bv_unsigned N)%Z) in *.
set (lo' := (((lo + page_size - 1) / page_size) * page_size)%Z) in *.
set (hi' := ((hi / page_size) * page_size)%Z) in *.
assert (Hlo0 : (0 <= lo')%Z).
{ subst lo'. unfold page_size.
  pose proof (Z.div_pos (lo + 4096 - 1) 4096 ltac:(lia) ltac:(lia)). nia. }
assert (Hhi0 : (hi' <= hi)%Z).
{ subst hi'. unfold page_size.
  pose proof (Z.div_mod hi 4096 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound hi 4096 ltac:(lia)) as B. lia. }
assert (Hhieq : hi = (lo + bv_unsigned N)%Z) by reflexivity.
assert (Hlo' : (lo <= lo')%Z).
{ subst lo'. unfold page_size.
  pose proof (Z.div_mod (lo + 4096 - 1) 4096 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (lo + 4096 - 1) 4096 ltac:(lia)) as B. lia. }
destruct (Z.ltb_spec lo' hi') as [Hc|Hc]; cbn [In] in Hin; [|destruct Hin].
destruct Hin as [Heq|[]]. injection Heq as <- <-.
rewrite u64 by lia. lia.
Qed.

(* A cut never manufactures an empty entry from a nonempty one: the left
   remnant is [min sz (lo - a)] with [a < lo], the right is
   [a + sz - max a hi] with [hi < a + sz], and both are positive.  This is
   the first conjunct of [maps_subtract_entry_inv], named on its own
   because the arms want it without the sub-interval. *)
Lemma maps_subtract_nz : forall L lo hi a n,
MapsFit.maps_fit L ->
(forall b m, In (b, m) L -> (0 < bv_unsigned m)%Z) ->
In (a, n) (maps_subtract L lo hi) -> (0 < bv_unsigned n)%Z.
Proof.
intros L lo hi a n Hfit Hnz Hin.
exact (proj1 (maps_subtract_entry_inv L lo hi a n Hfit Hnz Hin)).
Qed.

(* [LZ_NZ] at the start of every run: the ledger is [[]]. *)
Lemma init_config_LZ_NZ : forall segs pc ph sp brk0 mbase rnd lim inp,
LZ_NZ (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp)).
Proof.
intros segs pc ph sp brk0 mbase rnd lim inp a n Hin.
rewrite (init_lazy_nil segs pc ph sp brk0 mbase rnd lim inp) in Hin.
destruct Hin.
Qed.

(* An arm that leaves [m_vm] alone preserves it, as [WF_of_vm_eq] does for
   [WF] -- the ~78 non-writer arms of [checked_table] close with this. *)
Lemma LZ_NZ_of_vm_eq : forall m m', m_vm m' = m_vm m -> LZ_NZ m -> LZ_NZ m'.
Proof.
intros m m' E H. unfold LZ_NZ, m_vm_lazy in *. rewrite E. exact H.
Qed.

