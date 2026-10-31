(** * LinuxProcessSem.Checks.Sys.Mm.Mmap — the brk (214), mmap (222), munmap (215) checkers, and their proofs

    Mirrors [Sys/Mm/Mmap.v], which answers to Linux [mm/mmap.c]: this
    file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude Fs.ReadWrite.

Definition check_brk (req : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU r [] zs us [] [] =>
      if brk_r_ok m req r
         && listNN_eqb zs (brk_zeros req r (vm_brk (m_vmmaps m)))
         && listNN_eqb us (brk_unmaps r (vm_brk (m_vmmaps m)))
      then CheckOk (with_brk_next m req r) []
      else CheckReject
  | _ => CheckReject
  end.

Definition check_mmap (addr len prot flags fd off : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if negb (mmap_off_aligned_b off) then
    (if mmap_pglen_ok_b len
     then check_ret_only eff (errno_ret EINVAL) m []
     else CheckUnmodeled)
  else if negb (mmap_anon_b flags) then CheckUnmodeled
  else if w_is0 len then
    (if mmap_plain_anon_b flags
     then check_ret_only eff (errno_ret EINVAL) m []
     else CheckUnmodeled)
  else if mmap_modeled_b prot flags off then
  match eff with
  | mkEffectU r [] zs [] [] [] =>
      if errno_ret_in mmap_errnos r
      then match zs with [] => CheckOk m [] | _ => CheckReject end
      else
        let nZ := page_round_up_Z (bv_unsigned len) in
        let n := Z_to_bv 64 nZ in
        if (bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
           && (bv_unsigned r + nZ <=? alloc_top (m_vmmaps m))%Z
           && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) r n
           && mmap_noreserve_backed_ok flags m nZ
           && listNN_eqb zs [(r, n)]
        then CheckOk
               (with_mmap_backing flags r n
                (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                             ((r, n) :: vm_maps (m_vmmaps m))
                             (vm_noaccess (m_vmmaps m))
                             (vm_start_brk (m_vmmaps m))
                             (vm_brk (m_vmmaps m))
                             (vm_limit (m_vmmaps m))
                             (vm_mmap_base (m_vmmaps m))
                             (vm_init_sp (m_vmmaps m))) m)) []
        else CheckReject
  | _ => CheckReject
  end
  else if mmap_noaccess_b prot flags off then
  match eff with
  | mkEffectU r [] [] us [] [] =>
      if errno_ret_in mmap_errnos r
      then match us with [] => CheckOk m [] | _ => CheckReject end
      else
        let nZ := page_round_up_Z (bv_unsigned len) in
        let n := Z_to_bv 64 nZ in
        if (bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
           && (bv_unsigned r + nZ <=? alloc_top (m_vmmaps m))%Z
           && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) r n
           && listNN_eqb us [(r, n)]
        then CheckOk
               (with_mmap_backing flags r n
                (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                             ((r, n) :: vm_maps (m_vmmaps m))
                             ((r, n) :: vm_noaccess (m_vmmaps m))
                             (vm_start_brk (m_vmmaps m))
                             (vm_brk (m_vmmaps m))
                             (vm_limit (m_vmmaps m))
                             (vm_mmap_base (m_vmmaps m))
                             (vm_init_sp (m_vmmaps m))) m)) []
        else CheckReject
  | _ => CheckReject
  end
  else if mmap_fixed_noaccess_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z
    then check_ret_only eff (errno_ret ENOMEM) m []
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then CheckUnmodeled
    else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
    then check_ret_only eff (errno_ret EINVAL) m []
    else if negb (0 <? bv_unsigned addr)%Z then CheckUnmodeled
    else
      let n := Z_to_bv 64 nZ in
      if region_free (vm_reserved (m_vmmaps m)) addr n
         && map_contains (vm_maps (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] [] us [] [] =>
            if errno_ret_in mmap_errnos r
            then match us with
                 | [] => CheckOk m []                (* range preserved *)
                 | _ =>
                     if listNN_eqb us [(addr, n)]    (* range destroyed *)
                     then CheckOk
                       (with_mmap_destroyed addr n
                         (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
                     else CheckReject
                 end
            else if bv_eqb r addr && listNN_eqb us [(addr, n)]
            then CheckOk
              (with_mmap_replacement flags addr n
               (with_vmmaps
                (mkVmMapsFull (vm_reserved (m_vmmaps m))
                  (vm_maps (m_vmmaps m))
                  ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m))
                                  (bv_unsigned addr)
                                  (bv_unsigned addr + bv_unsigned n))
                  (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m))
                  (vm_limit (m_vmmaps m))
                             (vm_mmap_base (m_vmmaps m))
                             (vm_init_sp (m_vmmaps m))) m)) []
            else CheckReject
        | _ => CheckReject
        end
      else if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                          addr n
      then
        match eff with
        | mkEffectU r [] [] us [] [] =>
            if errno_ret_in mmap_errnos r
            then match us with [] => CheckOk m [] | _ => CheckReject end
            else if bv_eqb r addr && listNN_eqb us [(addr, n)]
            then CheckOk
                   (with_mmap_backing flags addr n
                    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                                 ((addr, n) :: vm_maps (m_vmmaps m))
                                 ((addr, n) :: vm_noaccess (m_vmmaps m))
                                 (vm_start_brk (m_vmmaps m))
                                 (vm_brk (m_vmmaps m))
                                 (vm_limit (m_vmmaps m))
                             (vm_mmap_base (m_vmmaps m))
                             (vm_init_sp (m_vmmaps m))) m)) []
            else CheckReject
        | _ => CheckReject
        end
      else if region_free (vm_reserved (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] [] us [] [] =>
            if errno_ret_in mmap_errnos r
            then match us with
                 | [] => CheckOk m []                (* range preserved *)
                 | _ =>
                     if listNN_eqb us [(addr, n)]    (* range destroyed *)
                     then CheckOk
                       (with_mmap_destroyed addr n
                         (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
                     else CheckReject
                 end
            else if bv_eqb r addr && listNN_eqb us [(addr, n)]
            then CheckOk
              (with_mmap_replacement flags addr n
               (with_vmmaps
                 (mmap_fixed_noaccess_span_next (m_vmmaps m) addr n) m)) []
            else CheckReject
        | _ => CheckReject
        end
      else CheckUnmodeled
  else if mmap_fixed_rw_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z
    then check_ret_only eff (errno_ret ENOMEM) m []
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then CheckUnmodeled
    else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
    then check_ret_only eff (errno_ret EINVAL) m []
    else if negb (0 <? bv_unsigned addr)%Z then CheckUnmodeled
    else
      let n := Z_to_bv 64 nZ in
      if region_free (vm_reserved (m_vmmaps m)) addr n
         && map_contains (vm_maps (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] zs us [] [] =>
            if errno_ret_in mmap_errnos r
            then match zs with
                 | _ :: _ => CheckReject       (* no failure exposes bytes *)
                 | [] =>
                     match us with
                     | [] => CheckOk m []               (* range preserved *)
                     | _ =>
                         if listNN_eqb us [(addr, n)]   (* range destroyed *)
                         then CheckOk
                           (with_mmap_destroyed addr n
                             (mmap_fixed_destroyed_next (m_vmmaps m) addr n)
                             m) []
                         else CheckReject
                     end
                 end
            else match us with
                 | _ :: _ => CheckReject       (* the success unmaps nothing *)
                 | [] =>
                     if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                        && mmap_fixed_rw_budget_ok flags m addr n
                     then CheckOk
                       (with_mmap_replacement flags addr n
                         (with_vmmaps
                           (mmap_fixed_rw_next (m_vmmaps m) addr n) m)) []
                     else CheckReject
                 end
        | _ => CheckReject
        end
      else if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                          addr n
      then
        match eff with
        | mkEffectU r [] zs [] [] [] =>
            if errno_ret_in mmap_errnos r
            then match zs with [] => CheckOk m [] | _ => CheckReject end
            else if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                    && mmap_noreserve_backed_ok flags m nZ
            then CheckOk
                   (with_mmap_backing flags addr n
                    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                                 ((addr, n) :: vm_maps (m_vmmaps m))
                                 (vm_noaccess (m_vmmaps m))
                                 (vm_start_brk (m_vmmaps m))
                                 (vm_brk (m_vmmaps m))
                                 (vm_limit (m_vmmaps m))
                             (vm_mmap_base (m_vmmaps m))
                             (vm_init_sp (m_vmmaps m))) m)) []
            else CheckReject
        | _ => CheckReject
        end
      else if region_free (vm_reserved (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] zs us [] [] =>
            if errno_ret_in mmap_errnos r
            then match zs with
                 | _ :: _ => CheckReject       (* no failure exposes bytes *)
                 | [] =>
                     match us with
                     | [] => CheckOk m []               (* range preserved *)
                     | _ =>
                         if listNN_eqb us [(addr, n)]   (* range destroyed *)
                         then CheckOk
                           (with_mmap_destroyed addr n
                             (mmap_fixed_destroyed_next (m_vmmaps m) addr n)
                             m) []
                         else CheckReject
                     end
                 end
            else match us with
                 | _ :: _ => CheckReject       (* the success unmaps nothing *)
                 | [] =>
                     if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                        && mmap_fixed_rw_span_budget_ok flags m addr n
                     then CheckOk
                       (with_mmap_replacement flags addr n
                         (with_vmmaps
                           (mmap_fixed_rw_span_next (m_vmmaps m) addr n) m)) []
                     else CheckReject
                 end
        | _ => CheckReject
        end
      else CheckUnmodeled
  else if mmap_noreplace_noaccess_b prot flags off then
    (* MAP_FIXED_NOREPLACE, PROT_NONE: the MAP_FIXED argument gate, then
       one split on the ledger — the free-range reservation, or -EEXIST
       beside the environment errno (see [Mmap.mmap_spec]). *)
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z
    then check_ret_only eff (errno_ret ENOMEM) m []
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then CheckUnmodeled
    else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
    then check_ret_only eff (errno_ret EINVAL) m []
    else if negb (0 <? bv_unsigned addr)%Z then CheckUnmodeled
    else
      let n := Z_to_bv 64 nZ in
      if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] [] us [] [] =>
            if errno_ret_in mmap_errnos r
            then match us with [] => CheckOk m [] | _ => CheckReject end
            else if bv_eqb r addr && listNN_eqb us [(addr, n)]
            then CheckOk
                   (with_mmap_backing flags addr n
                    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                                 ((addr, n) :: vm_maps (m_vmmaps m))
                                 ((addr, n) :: vm_noaccess (m_vmmaps m))
                                 (vm_start_brk (m_vmmaps m))
                                 (vm_brk (m_vmmaps m))
                                 (vm_limit (m_vmmaps m))
                                 (vm_mmap_base (m_vmmaps m))
                                 (vm_init_sp (m_vmmaps m))) m)) []
            else CheckReject
        | _ => CheckReject
        end
      else
        match eff with
        | mkEffectU r [] [] [] [] [] =>
            if errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST)
            then CheckOk m [] else CheckReject
        | _ => CheckReject
        end
  else if mmap_noreplace_rw_b prot flags off then
    (* MAP_FIXED_NOREPLACE, rw: the same gate and split, with the rw
       free-range grant and its budget conjunct. *)
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z
    then check_ret_only eff (errno_ret ENOMEM) m []
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then CheckUnmodeled
    else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
    then check_ret_only eff (errno_ret EINVAL) m []
    else if negb (0 <? bv_unsigned addr)%Z then CheckUnmodeled
    else
      let n := Z_to_bv 64 nZ in
      if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] zs [] [] [] =>
            if errno_ret_in mmap_errnos r
            then match zs with [] => CheckOk m [] | _ => CheckReject end
            else if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                    && mmap_noreserve_backed_ok flags m nZ
            then CheckOk
                   (with_mmap_backing flags addr n
                    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                                 ((addr, n) :: vm_maps (m_vmmaps m))
                                 (vm_noaccess (m_vmmaps m))
                                 (vm_start_brk (m_vmmaps m))
                                 (vm_brk (m_vmmaps m))
                                 (vm_limit (m_vmmaps m))
                                 (vm_mmap_base (m_vmmaps m))
                                 (vm_init_sp (m_vmmaps m))) m)) []
            else CheckReject
        | _ => CheckReject
        end
      else
        match eff with
        | mkEffectU r [] [] [] [] [] =>
            if errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST)
            then CheckOk m [] else CheckReject
        | _ => CheckReject
        end
  else CheckUnmodeled.

Definition check_munmap (addr len : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    let nZ := page_round_up_Z (bv_unsigned len) in
    (* the range leaves the user address space: see [Mmap.munmap_spec] *)
    if (TASK_SIZE <? bv_unsigned addr + nZ)%Z
    then check_ret_only eff (errno_ret EINVAL) m []
    else
    let n := Z_to_bv 64 nZ in
    if map_has (vm_maps (m_vmmaps m)) addr n then
      match eff with
      | mkEffectU r [] [] us [] [] =>
          if errno_ret_in munmap_errnos r
          then match us with
               | [] => CheckOk m []
               | _ => CheckReject
               end
          else if w_is0 r && listNN_eqb us [(addr, n)]
          then CheckOk (with_mmap_destroyed addr n
                          (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
          else CheckReject
      | _ => CheckReject
      end
    else if munmap_free_ok (m_vmmaps m) addr nZ
    then check_ret_only eff (Z_to_bv 64 0) m []
    else if munmap_cut_ok (m_vmmaps m) addr nZ then
      match eff with
      | mkEffectU r [] [] us [] [] =>
          if errno_ret_in munmap_errnos r
          then match us with
               | [] => CheckOk m []
               | _ => CheckReject
               end
          else if w_is0 r && listNN_eqb us [(addr, n)]
          then CheckOk (with_mmap_destroyed addr n
                          (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
          else CheckReject
      | _ => CheckReject
      end
    else CheckUnmodeled.

(** Mirrors [Mremap.mremap_spec] gate for gate, in Linux's order.  The one
    structural difference is the equal-size arm: it sits OUTSIDE the errno
    dispatch, because Linux cannot fail an equal-size call for lack of
    memory (mm/mremap.c:1041-1093, v6.12 — see [mremap_spec]).  So a trace
    reporting [-ENOMEM] for [old_len = new_len] on a modeled source is
    rejected, not accepted. *)

(** mprotect: the four argument gates Linux decides first, in its order —
    the PROT_GROWSDOWN|PROT_GROWSUP conflict, then alignment, then a zero
    [len] that returns 0 for any surviving [prot], then a page-rounded end
    that wraps past 2^64 and is -ENOMEM for any surviving [prot] (see
    [Mprotect.mprotect_spec] for the citations).  Only past those is the
    [prot] interpreted: at
    nonzero length just the rw permissions the model's memory already has
    are modeled ([Mprotect.mprotect_modeled_b]); any other [prot] — PROT_EXEC
    above all — is fail-closed. *)

(** getrandom: destination must be writable-mapped; then a nonzero
    request of at most [Random.getrandom_small_max] bytes is exactly
    [cap] arbitrary bytes written at [buf], and a larger one is either
    an error return with no writes or arbitrary bytes written at [buf]
    — at least one (a bare 0 return is admissible only for [cap = 0])
    — and only flags 0 / GRND_NONBLOCK are modeled (see
    [Random.getrandom_spec]). *)

(** The acceptor for a ZERO-BYTE getrandom request once the range
    verdict is known: [r0] is what that verdict allows besides the
    interrupted return, which stays admissible either way (Linux can be
    interrupted before it imports the buffer). *)

Lemma page_round_up_Z_nonneg : forall z,
  (0 <= z)%Z -> (0 <= page_round_up_Z z)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  apply Z.mul_nonneg_nonneg; [|lia].
  apply Z.div_pos; lia.
Qed.

Lemma page_round_up_Z_mono : forall a b,
  (a <= b)%Z -> (page_round_up_Z a <= page_round_up_Z b)%Z.
Proof.
  intros a b H. unfold page_round_up_Z, page_size.
  apply Z.mul_le_mono_nonneg_r; [lia|].
  apply Z.div_le_mono; lia.
Qed.

(** Turn a boolean goal condition into [true] using equalities and
    arithmetic facts already in context (robust to hypothesis naming). *)

Lemma check_brk_sound_ok : forall req eff m m' evs i,
  check_brk req eff m = CheckOk m' evs -> brk_spec req i m (Ok eff m' evs).
Proof.
  intros req eff m m' evs i H.
  unfold check_brk in H. unfold brk_spec.
  destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
    [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]; try discriminate.
  destruct (brk_r_ok m req r) eqn:HR; [|discriminate].
  destruct (listNN_eqb zs (brk_zeros req r (vm_brk (m_vmmaps m)))) eqn:HZs;
    [|cbn [andb] in H; discriminate].
  destruct (listNN_eqb us (brk_unmaps r (vm_brk (m_vmmaps m)))) eqn:HUs;
    [|cbn [andb] in H; discriminate].
  apply listNN_eqb_eq in HZs; subst zs.
  apply listNN_eqb_eq in HUs; subst us.
  cbn [andb] in H. inversion H; clear H; subst.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  eapply bind_ok0; [apply (choose_ok _ r); exact HR|].
  eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_brk_sound_unmodeled : forall req eff m i,
  check_brk req eff m = CheckUnmodeled -> brk_spec req i m Unmodeled.
Proof.
  intros req [r ws zs us cs copyins] m i H. unfold check_brk in H.
  destruct ws; [destruct cs; [destruct copyins|]|].
  - destruct (brk_r_ok m req r
              && listNN_eqb zs (brk_zeros req r (vm_brk (m_vmmaps m)))
              && listNN_eqb us (brk_unmaps r (vm_brk (m_vmmaps m))));
      discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
Qed.

Lemma check_brk_complete_ok : forall req eff m m' evs i,
  brk_spec req i m (Ok eff m' evs) -> check_brk req eff m = CheckOk m' evs.
Proof.
  intros req eff m m' evs i H.
  unfold brk_spec in H. sys_unfold. cbv iota in H. inv_ok.
  unfold check_brk. cbv iota.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
  match goal with H : ?b = true |- context [ ?b ] => rewrite H end.
  reflexivity.
Qed.

Lemma check_brk_complete_unmodeled : forall req m i eff,
  brk_spec req i m Unmodeled -> check_brk req eff m = CheckUnmodeled.
Proof.
  intros req m i eff H.
  unfold brk_spec in H. sys_unfold. cbv iota in H. inv_ok; discriminate.
Qed.

(* ------------------------------------------------------------------ mmap *)

Lemma check_mmap_sound_ok : forall addr len prot flags fd off eff m m' evs i,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs).
Proof.
  intros addr len prot flags fd off eff m m' evs i H.
  unfold check_mmap in H. unfold mmap_spec.
  destruct (negb (mmap_off_aligned_b off)) eqn:Hoff.
  { destruct (mmap_pglen_ok_b len) eqn:Hpl; [|discriminate].
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (negb (mmap_anon_b flags)) eqn:Hanon; [discriminate|].
  destruct (w_is0 len) eqn:Hl.
  { destruct (mmap_plain_anon_b flags) eqn:Hpa; [|discriminate].
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (mmap_modeled_b prot flags off) eqn:Hrw.
  { destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
      [destruct us as [|? ?];
        [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|];
      try discriminate.
    destruct (errno_ret_in mmap_errnos r) eqn:He.
    - destruct zs as [|? ?]; [|discriminate].
      inversion H; clear H; subst.
      apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
      apply alt_l. eapply bind_ok0.
      { apply (choose_ok _ e). exact HIn. }
      apply pure_ok.
    - cbv zeta in H.
      destruct ((bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
                && (bv_unsigned r + page_round_up_Z (bv_unsigned len) <=? alloc_top (m_vmmaps m))%Z
                && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                     r (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                 && mmap_noreserve_backed_ok flags m
                     (page_round_up_Z (bv_unsigned len))
                && listNN_eqb zs [(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
        eqn:HC; [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in HC as [HC HZs].
      apply andb_true_iff in HC as [HC HL].
      apply andb_true_iff in HC as [HC HD].
      apply andb_true_iff in HC as [HC HB].
      apply andb_true_iff in HC as [HA HZ].
      apply Z.eqb_eq in HA. apply Z.ltb_lt in HZ. apply Z.leb_le in HB.
      apply listNN_eqb_eq in HZs; subst zs.
      apply alt_r.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
      eapply bind_ok0.
      { apply (choose_ok _ r). cbv beta. repeat split; assumption. }
      eapply bind_ok0; [apply modify_ok|].
      apply pure_ok. }
  destruct (mmap_noaccess_b prot flags off) eqn:Hnone.
  { destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
      [destruct zs as [|? ?]|]; try discriminate.
    destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
    destruct (errno_ret_in mmap_errnos r) eqn:He.
    - destruct us as [|? ?]; [|discriminate].
      inversion H; clear H; subst.
      apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
      apply alt_l. eapply bind_ok0.
      { apply (choose_ok _ e). exact HIn. }
      apply pure_ok.
    - cbv zeta in H.
      destruct ((bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
                && (bv_unsigned r + page_round_up_Z (bv_unsigned len) <=? alloc_top (m_vmmaps m))%Z
                && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                     r (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                && listNN_eqb us
                     [(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
        eqn:HC; [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in HC as [HC HUs].
      apply andb_true_iff in HC as [HC HD].
      apply andb_true_iff in HC as [HC HB].
      apply andb_true_iff in HC as [HA HZ].
      apply Z.eqb_eq in HA. apply Z.ltb_lt in HZ. apply Z.leb_le in HB.
      apply listNN_eqb_eq in HUs; subst us.
      apply alt_r.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
      eapply bind_ok0.
      { apply (choose_ok _ r). cbv beta. repeat split; assumption. }
      eapply bind_ok0; [apply modify_ok|].
      apply pure_ok. }
  destruct (mmap_fixed_noaccess_b prot flags off) eqn:Hfixed.
  { cbv zeta in H. cbv zeta.
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hovf.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                    <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil; [discriminate|].
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos; [discriminate|].
  destruct (region_free (vm_reserved (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  2: {
  destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                 addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
    eqn:Hfresh0.
  2: {
    (* SPANNING: the request meets live mappings without being contained
       in one, and stays clear of the image reservations. *)
    destruct (region_free (vm_reserved (m_vmmaps m)) addr
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
      eqn:Hspan; [|discriminate].
    destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
      [destruct zs as [|? ?]|]; try discriminate.
    destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
    destruct (errno_ret_in mmap_errnos r) eqn:He.
    - apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
      destruct us as [|u us].
      + (* errno, range preserved *)
        inversion H; clear H; subst.
        apply alt_l.
        eapply bind_ok0; [apply (choose_ok _ e); exact HIn|]. apply pure_ok.
      + (* errno, range destroyed *)
        destruct (listNN_eqb (u :: us)
                    [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
          eqn:Hus; [|discriminate].
        inversion H; clear H; subst.
        apply listNN_eqb_eq in Hus. rewrite Hus.
        apply alt_r. apply alt_r.
        eapply bind_ok0; [apply (choose_ok _ e); exact HIn|].
        eapply bind_ok0; [apply modify_ok|].
        apply pure_ok.
    - destruct (bv_eqb r addr
                && listNN_eqb us
                     [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
        eqn:HC; [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in HC as [Hr Hus].
      apply bv_eqb_eq in Hr; subst r.
      apply listNN_eqb_eq in Hus; subst us.
      apply alt_r. apply alt_l.
      eapply bind_ok0; [apply modify_ok|].
      apply pure_ok. }
    destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
      [destruct zs as [|? ?]|]; try discriminate.
    destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
    destruct (errno_ret_in mmap_errnos r) eqn:He.
    - destruct us as [|? ?]; [|discriminate].
      inversion H; clear H; subst.
      apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
      apply alt_l.
      eapply bind_ok0; [apply (choose_ok _ e); exact HIn|]. apply pure_ok.
    - destruct (bv_eqb r addr
                && listNN_eqb us
                     [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
        eqn:HC; [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in HC as [Hr Hus].
      apply bv_eqb_eq in Hr; subst r.
      apply listNN_eqb_eq in Hus; subst us.
      apply alt_r.
      eapply bind_ok0.
      { apply (choose_ok _ addr). reflexivity. }
      eapply bind_ok0; [apply modify_ok|].
      apply pure_ok. }
  destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
    [destruct zs as [|? ?]|]; try discriminate.
  destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
  destruct (errno_ret_in mmap_errnos r) eqn:He.
  - apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    destruct us as [|u us].
    + (* errno, range preserved *)
      inversion H; clear H; subst.
      apply alt_l.
      eapply bind_ok0; [apply (choose_ok _ e); exact HIn|]. apply pure_ok.
    + (* errno, range destroyed *)
      destruct (listNN_eqb (u :: us)
                  [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
        eqn:Hus; [|discriminate].
      inversion H; clear H; subst.
      apply listNN_eqb_eq in Hus. rewrite Hus.
      apply alt_r. apply alt_r.
      eapply bind_ok0; [apply (choose_ok _ e); exact HIn|].
      eapply bind_ok0; [apply modify_ok|].
      apply pure_ok.
  - destruct (bv_eqb r addr
              && listNN_eqb us
                   [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
      eqn:HC; [|discriminate].
    inversion H; clear H; subst.
    apply andb_true_iff in HC as [Hr Hus].
    apply bv_eqb_eq in Hr; subst r.
    apply listNN_eqb_eq in Hus; subst us.
    apply alt_r. apply alt_l.
    eapply bind_ok0; [apply modify_ok|].
    apply pure_ok. }
  destruct (mmap_fixed_rw_b prot flags off) eqn:Hfrw.
  2: {
    (* MAP_FIXED_NOREPLACE, both prot words: the gate, then the
       free-range grant or the -EEXIST beside the environment errno. *)
    destruct (mmap_noreplace_noaccess_b prot flags off) eqn:Hnrn.
    { cbv zeta in H. cbv zeta.
      destruct ((two_pow_64
                 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
        eqn:Hovf.
      { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
        apply pure_ok. }
      eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
      destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                        <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil; [discriminate|].
      destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
      { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
        apply pure_ok. }
      destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos; [discriminate|].
      destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                     addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
        eqn:Hfree.
      - destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
          [destruct zs as [|? ?]|]; try discriminate.
        destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
        destruct (errno_ret_in mmap_errnos r) eqn:He.
        + destruct us as [|? ?]; [|discriminate].
          inversion H; clear H; subst.
          apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
          apply alt_l.
          eapply bind_ok0; [apply (choose_ok _ e); exact HIn|]. apply pure_ok.
        + destruct (bv_eqb r addr
                    && listNN_eqb us
                         [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
            eqn:HC; [|discriminate].
          inversion H; clear H; subst.
          apply andb_true_iff in HC as [Hr Hus].
          apply bv_eqb_eq in Hr; subst r.
          apply listNN_eqb_eq in Hus; subst us.
          apply alt_r.
          eapply bind_ok0.
          { apply (choose_ok _ addr). reflexivity. }
          eapply bind_ok0; [apply modify_ok|].
          apply pure_ok.
      - destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
          [destruct zs as [|? ?]|]; try discriminate.
        destruct us as [|? ?];
          [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|];
          try discriminate.
        destruct (errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST))
          eqn:He; [|discriminate].
        inversion H; clear H; subst.
        apply orb_true_iff in He as [He | He].
        + apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
          apply alt_l.
          eapply bind_ok0; [apply (choose_ok _ e); exact HIn|]. apply pure_ok.
        + apply bv_eqb_eq in He; subst r.
          apply alt_r. apply pure_ok. }
    destruct (mmap_noreplace_rw_b prot flags off) eqn:Hnrr; [|discriminate].
    cbv zeta in H. cbv zeta.
    destruct ((two_pow_64
               <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
      eqn:Hovf.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      apply pure_ok. }
    eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
    destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                      <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil; [discriminate|].
    destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      apply pure_ok. }
    destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos; [discriminate|].
    destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                   addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
      eqn:Hfree.
    - destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
        [destruct us as [|? ?];
          [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|];
        try discriminate.
      destruct (errno_ret_in mmap_errnos r) eqn:He.
      + destruct zs as [|? ?]; [|discriminate].
        inversion H; clear H; subst.
        apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
        apply alt_l.
        eapply bind_ok0; [apply (choose_ok _ e); exact HIn|]. apply pure_ok.
      + destruct (bv_eqb r addr
                  && listNN_eqb zs
                       [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]
                  && mmap_noreserve_backed_ok flags m
                       (page_round_up_Z (bv_unsigned len)))
          eqn:HC; [|discriminate].
        inversion H; clear H; subst.
        apply andb_true_iff in HC as [HC Hbud].
        apply andb_true_iff in HC as [Hr Hzs].
        apply bv_eqb_eq in Hr; subst r.
        apply listNN_eqb_eq in Hzs; subst zs.
        apply alt_r.
        eapply bind_ok0.
        { apply (choose_ok _ addr). cbv beta. split; [reflexivity|assumption]. }
        eapply bind_ok0; [apply modify_ok|].
        apply pure_ok.
    - destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
        [destruct zs as [|? ?]|]; try discriminate.
      destruct us as [|? ?];
        [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|];
        try discriminate.
      destruct (errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST))
        eqn:He; [|discriminate].
      inversion H; clear H; subst.
      apply orb_true_iff in He as [He | He].
      + apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
        apply alt_l.
        eapply bind_ok0; [apply (choose_ok _ e); exact HIn|]. apply pure_ok.
      + apply bv_eqb_eq in He; subst r.
        apply alt_r. apply pure_ok. }
  cbv zeta in H. cbv zeta.
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hovf.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                    <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil; [discriminate|].
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos; [discriminate|].
  destruct (region_free (vm_reserved (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  { destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?]; try discriminate.
  destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
  destruct (errno_ret_in mmap_errnos r) eqn:He.
  - apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|u us].
    + (* errno, range preserved *)
      inversion H; clear H; subst.
      apply alt_l.
      eapply bind_ok0; [apply (choose_ok _ e); exact HIn|]. apply pure_ok.
    + (* errno, range destroyed *)
      destruct (listNN_eqb (u :: us)
                  [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
        eqn:Hus; [|discriminate].
      inversion H; clear H; subst.
      apply listNN_eqb_eq in Hus. rewrite Hus.
      apply alt_r. apply alt_r.
      eapply bind_ok0; [apply (choose_ok _ e); exact HIn|].
      eapply bind_ok0; [apply modify_ok|].
      apply pure_ok.
  - destruct us as [|? ?]; [|discriminate].
    destruct (bv_eqb r addr
              && listNN_eqb zs
                   [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]
              && mmap_fixed_rw_budget_ok flags m addr
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
      eqn:HC; [|discriminate].
    inversion H; clear H; subst.
    apply andb_true_iff in HC as [HC Hbacked].
    apply andb_true_iff in HC as [Hr Hzs].
    apply bv_eqb_eq in Hr; subst r.
    apply listNN_eqb_eq in Hzs; subst zs.
    apply alt_r. apply alt_l.
    eapply bind_ok0; [apply (choose_ok _ tt); exact Hbacked|].
    eapply bind_ok0; [apply modify_ok|].
    apply pure_ok. }
  destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                 addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                 ) eqn:Hfresh.
  2: {
    (* SPANNING, the rw half. *)
    destruct (region_free (vm_reserved (m_vmmaps m)) addr
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
      eqn:Hspan; [|discriminate].
    destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
      try discriminate.
    destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
    destruct (errno_ret_in mmap_errnos r) eqn:He.
    - apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
      destruct zs as [|? ?]; [|discriminate].
      destruct us as [|u us].
      + (* errno, range preserved *)
        inversion H; clear H; subst.
        apply alt_l.
        eapply bind_ok0; [apply (choose_ok _ e); exact HIn|]. apply pure_ok.
      + (* errno, range destroyed *)
        destruct (listNN_eqb (u :: us)
                    [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
          eqn:Hus; [|discriminate].
        inversion H; clear H; subst.
        apply listNN_eqb_eq in Hus. rewrite Hus.
        apply alt_r. apply alt_r.
        eapply bind_ok0; [apply (choose_ok _ e); exact HIn|].
        eapply bind_ok0; [apply modify_ok|].
        apply pure_ok.
    - destruct us as [|? ?]; [|discriminate].
      destruct (bv_eqb r addr
                && listNN_eqb zs
                     [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]
                && mmap_fixed_rw_span_budget_ok flags m addr
                     (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
        eqn:HC; [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in HC as [HC Hbacked].
      apply andb_true_iff in HC as [Hr Hzs].
      apply bv_eqb_eq in Hr; subst r.
      apply listNN_eqb_eq in Hzs; subst zs.
      apply alt_r. apply alt_l.
      eapply bind_ok0; [apply (choose_ok _ tt); exact Hbacked|].
      eapply bind_ok0; [apply modify_ok|].
      apply pure_ok. }
  destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
    [destruct us as [|? ?];
      [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|];
    try discriminate.
  destruct (errno_ret_in mmap_errnos r) eqn:He.
  - destruct zs as [|? ?]; [|discriminate].
    inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    apply alt_l.
    eapply bind_ok0; [apply (choose_ok _ e); exact HIn|]. apply pure_ok.
  - destruct (bv_eqb r addr
              && listNN_eqb zs
                   [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]
              && mmap_noreserve_backed_ok flags m
                   (page_round_up_Z (bv_unsigned len)))
      eqn:HC; [|discriminate].
    inversion H; clear H; subst.
    apply andb_true_iff in HC as [HC Hbud].
    apply andb_true_iff in HC as [Hr Hzs].
    apply bv_eqb_eq in Hr; subst r.
    apply listNN_eqb_eq in Hzs; subst zs.
    apply alt_r.
    eapply bind_ok0.
    { apply (choose_ok _ addr). cbv beta. split; [reflexivity|assumption]. }
    eapply bind_ok0; [apply modify_ok|].
    apply pure_ok.
Qed.

Lemma check_mmap_sound_unmodeled : forall addr len prot flags fd off eff m i,
  check_mmap addr len prot flags fd off eff m = CheckUnmodeled ->
  mmap_spec addr len prot flags fd off i m Unmodeled.
Proof.
  intros addr len prot flags fd off [r ws zs us cs copyins] m i H.
  unfold check_mmap in H. unfold mmap_spec.
  destruct (negb (mmap_off_aligned_b off)) eqn:Hoff.
  { destruct (mmap_pglen_ok_b len) eqn:Hpl;
      [now apply check_ret_only_no_unmodeled in H | apply unmodeled_intro]. }
  destruct (negb (mmap_anon_b flags)) eqn:Hanon; [apply unmodeled_intro|].
  destruct (w_is0 len) eqn:Hl.
  { destruct (mmap_plain_anon_b flags) eqn:Hpa;
      [now apply check_ret_only_no_unmodeled in H | apply unmodeled_intro]. }
  destruct (mmap_modeled_b prot flags off) eqn:Hrw.
  { exfalso. destruct ws;
      [destruct us; [destruct cs; [destruct copyins|]|]|].
    + destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      cbv zeta in H.
      destruct ((bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
                && (bv_unsigned r + page_round_up_Z (bv_unsigned len) <=? alloc_top (m_vmmaps m))%Z
                && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                     r (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                 && mmap_noreserve_backed_ok flags m
                     (page_round_up_Z (bv_unsigned len))
                && listNN_eqb zs
                     [(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]);
        discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate. }
  destruct (mmap_noaccess_b prot flags off) eqn:Hnone.
  { exfalso. destruct ws;
      [destruct zs; [destruct cs; [destruct copyins|]|]|];
      try discriminate.
    destruct (errno_ret_in mmap_errnos r).
    - destruct us; discriminate.
    - cbv zeta in H.
      destruct ((bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
                && (bv_unsigned r + page_round_up_Z (bv_unsigned len) <=? alloc_top (m_vmmaps m))%Z
                && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                     r (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                && listNN_eqb us
                     [(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]);
        discriminate. }
  destruct (mmap_fixed_noaccess_b prot flags off) eqn:Hfixed.
  2: {
  destruct (mmap_fixed_rw_b prot flags off) eqn:Hfrw.
  2: {
    (* MAP_FIXED_NOREPLACE: the checker declines only at the two gates
       the spec declines at, and answers on both ledger sub-cases. *)
    destruct (mmap_noreplace_noaccess_b prot flags off) eqn:Hnrn.
    { cbv zeta in H. cbv zeta.
      destruct ((two_pow_64
                 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
        eqn:Hovf.
      { now apply check_ret_only_no_unmodeled in H. }
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
      destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                        <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil.
      { apply unmodeled_intro. }
      destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
      { now apply check_ret_only_no_unmodeled in H. }
      destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos.
      { apply unmodeled_intro. }
      exfalso.
      destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                     addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
        eqn:Hfree.
      - destruct ws;
          [destruct zs; [destruct cs; [destruct copyins|]|]|];
          try discriminate.
        destruct (errno_ret_in mmap_errnos r).
        + destruct us; discriminate.
        + destruct (bv_eqb r addr
                    && listNN_eqb us
                         [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]);
            discriminate.
      - destruct ws;
          [destruct zs; [destruct us; [destruct cs; [destruct copyins|]|]|]|];
          try discriminate.
        destruct (errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST));
          discriminate. }
    destruct (mmap_noreplace_rw_b prot flags off) eqn:Hnrr.
    2: { apply unmodeled_intro. }
    cbv zeta in H. cbv zeta.
    destruct ((two_pow_64
               <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
      eqn:Hovf.
    { now apply check_ret_only_no_unmodeled in H. }
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
    destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                      <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil.
    { apply unmodeled_intro. }
    destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos.
    { apply unmodeled_intro. }
    exfalso.
    destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                   addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
      eqn:Hfree.
    - destruct ws;
        [destruct us; [destruct cs; [destruct copyins|]|]|];
        try discriminate.
      destruct (errno_ret_in mmap_errnos r).
      + destruct zs; discriminate.
      + destruct (bv_eqb r addr
                  && listNN_eqb zs
                       [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]
                  && mmap_noreserve_backed_ok flags m
                       (page_round_up_Z (bv_unsigned len)));
          discriminate.
    - destruct ws;
        [destruct zs; [destruct us; [destruct cs; [destruct copyins|]|]|]|];
        try discriminate.
      destruct (errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST));
        discriminate. }
  cbv zeta in H. cbv zeta.
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hovf.
  { now apply check_ret_only_no_unmodeled in H. }
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                    <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil.
  { apply unmodeled_intro. }
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos.
  { apply unmodeled_intro. }
  destruct (region_free (vm_reserved (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  2: { destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                      addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                      ) eqn:Hfresh.
       2: { destruct (region_free (vm_reserved (m_vmmaps m)) addr
                        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
              eqn:Hspan.
            2: {
                 apply unmodeled_intro. }
            (* the spanning branch answers, so it never yields
               [CheckUnmodeled] *)
            exfalso. destruct ws; try discriminate.
            destruct cs; [destruct copyins|]; try discriminate.
            destruct (errno_ret_in mmap_errnos r).
            - destruct zs; [|discriminate].
              destruct us as [|u us]; [discriminate|].
              destruct (listNN_eqb (u :: us)
                          [(addr, Z_to_bv 64
                                    (page_round_up_Z (bv_unsigned len)))]);
                discriminate.
            - destruct us; [|discriminate].
              destruct (bv_eqb r addr
                        && listNN_eqb zs
                             [(addr, Z_to_bv 64
                                       (page_round_up_Z (bv_unsigned len)))]
                        && mmap_fixed_rw_span_budget_ok flags m addr
                             (Z_to_bv 64
                                (page_round_up_Z (bv_unsigned len))));
                discriminate. }
       exfalso. destruct ws;
         [destruct us; [destruct cs; [destruct copyins|]|]|];
         try discriminate.
       destruct (errno_ret_in mmap_errnos r).
       - destruct zs; discriminate.
       - destruct (bv_eqb r addr
                   && listNN_eqb zs
                        [(addr, Z_to_bv 64
                                  (page_round_up_Z (bv_unsigned len)))]
                   && mmap_noreserve_backed_ok flags m
                        (page_round_up_Z (bv_unsigned len)));
           discriminate. }
  exfalso. destruct ws;
    [destruct cs; [destruct copyins|]|]; try discriminate.
  destruct (errno_ret_in mmap_errnos r).
  - destruct zs; [|discriminate].
    destruct us as [|u us]; [discriminate|].
    destruct (listNN_eqb (u :: us)
                [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]);
      discriminate.
  - destruct us; [|discriminate].
    destruct (bv_eqb r addr
              && listNN_eqb zs
                   [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]
              && mmap_fixed_rw_budget_ok flags m addr
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))));
      discriminate. }
  cbv zeta in H. cbv zeta.
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hovf.
  { now apply check_ret_only_no_unmodeled in H. }
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                    <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil.
  { apply unmodeled_intro. }
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos.
  { apply unmodeled_intro. }
  destruct (region_free (vm_reserved (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  2: {
  destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                 addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
    eqn:Hfresh0.
       2: { destruct (region_free (vm_reserved (m_vmmaps m)) addr
                        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
              eqn:Hspan.
            2: {
                 apply unmodeled_intro. }
            (* the spanning branch answers, so it never yields
               [CheckUnmodeled] *)
            exfalso. destruct ws;
              [destruct zs; [destruct cs; [destruct copyins|]|]|];
              try discriminate.
            destruct (errno_ret_in mmap_errnos r).
            - destruct us as [|u us]; [discriminate|].
              destruct (listNN_eqb (u :: us)
                          [(addr, Z_to_bv 64
                                    (page_round_up_Z (bv_unsigned len)))]);
                discriminate.
            - destruct (bv_eqb r addr
                        && listNN_eqb us
                             [(addr, Z_to_bv 64
                                       (page_round_up_Z (bv_unsigned len)))]);
                discriminate. }
       exfalso. destruct ws;
         [destruct zs; [destruct cs; [destruct copyins|]|]|];
         try discriminate.
       destruct (errno_ret_in mmap_errnos r).
       - destruct us; discriminate.
       - destruct (bv_eqb r addr
                   && listNN_eqb us
                        [(addr, Z_to_bv 64
                                  (page_round_up_Z (bv_unsigned len)))]);
           discriminate. }
  exfalso. destruct ws;
    [destruct zs; [destruct cs; [destruct copyins|]|]|];
    try discriminate.
  destruct (errno_ret_in mmap_errnos r).
  - destruct us as [|u us]; [discriminate|].
    destruct (listNN_eqb (u :: us)
                [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]);
      discriminate.
  - destruct (bv_eqb r addr
              && listNN_eqb us
                   [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]);
      discriminate.
Qed.

Lemma check_mmap_complete_ok : forall addr len prot flags fd off eff m m' evs i,
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs) ->
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs.
Proof.
  intros addr len prot flags fd off eff m m' evs i H.
  unfold mmap_spec in H.
  unfold check_mmap.
  destruct (negb (mmap_off_aligned_b off)) eqn:Hoff.
  { destruct (mmap_pglen_ok_b len) eqn:Hpl; sys_unfold; inv_ok.
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
  destruct (negb (mmap_anon_b flags)) eqn:Hanon; [sys_unfold; inv_ok|].
  destruct (w_is0 len) eqn:Hl.
  { destruct (mmap_plain_anon_b flags) eqn:Hpa; sys_unfold; inv_ok.
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
  destruct (mmap_modeled_b prot flags off) eqn:Hrw; cbn [negb].
  { sys_unfold. cbv iota in H. inv_ok.
    - cbv zeta.
      match goal with
      | |- context [errno_ret_in ?es (errno_ret ?e)] =>
          rewrite (errno_ret_in_intro es e) by assumption
      end.
      reflexivity.
    - cbv zeta.
      pose proof (word_unsigned_range len) as Hlen.
      pose proof (page_round_up_Z_nonneg (bv_unsigned len) ltac:(lia)) as Hn.
      match goal with
      | Hb : (bv_unsigned ?a + _ <= _)%Z |- context [errno_ret_in ?es ?a] =>
          rewrite (errno_ret_in_below es a) by
            first [ reflexivity
                  | alloc_top_bounds;
                      unfold two_pow_64 in *; lia ]
      end.
      bool_true. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
      rewrite Bool.andb_true_r. reflexivity. }
  destruct (mmap_noaccess_b prot flags off) eqn:Hnone.
  { sys_unfold. cbv iota in H. inv_ok.
    - cbv zeta.
      match goal with
      | |- context [errno_ret_in ?es (errno_ret ?e)] =>
          rewrite (errno_ret_in_intro es e) by assumption
      end.
      reflexivity.
    - cbv zeta.
      pose proof (word_unsigned_range len) as Hlen.
      pose proof (page_round_up_Z_nonneg (bv_unsigned len) ltac:(lia)) as Hn.
      match goal with
      | Hb : (bv_unsigned ?a + _ <= _)%Z |- context [errno_ret_in ?es ?a] =>
          rewrite (errno_ret_in_below es a) by
            first [ reflexivity
                  | alloc_top_bounds;
                      unfold two_pow_64 in *; lia ]
      end.
      bool_true. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
      rewrite Bool.andb_true_r. reflexivity. }
  destruct (mmap_fixed_noaccess_b prot flags off) eqn:Hfixed.
  2: {
  destruct (mmap_fixed_rw_b prot flags off) eqn:Hfrw.
  2: {
    (* MAP_FIXED_NOREPLACE: every resolution the spec admits is one the
       checker accepts — the gate's errnos, the free-range grant, and
       the -EEXIST or environment errno on an occupied range. *)
    destruct (mmap_noreplace_noaccess_b prot flags off) eqn:Hnrn.
    { cbv zeta in H. cbv zeta.
      destruct ((two_pow_64
                 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
        eqn:Hovf.
      { sys_unfold. inv_ok.
        cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
      apply get_model_bind_ok_inv in H. cbv beta in H.
      destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                        <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil.
      { sys_unfold. inv_ok; discriminate. }
      destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
      { sys_unfold. inv_ok.
        cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
      destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos.
      { sys_unfold. inv_ok; discriminate. }
      apply negb_false_iff, Z.leb_le in Hceil.
      pose proof (word_unsigned_range addr) as Haddr.
      pose proof (word_unsigned_range len) as Hlen.
      pose proof (page_round_up_Z_nonneg (bv_unsigned len) ltac:(lia)) as Hn.
      destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                     addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
        eqn:Hfree.
      - sys_unfold. cbv iota in H. inv_ok.
        + (* errno *)
          cbv zeta.
          match goal with
          | |- context [errno_ret_in ?es (errno_ret ?e)] =>
              rewrite (errno_ret_in_intro es e) by assumption
          end.
          reflexivity.
        + (* the reservation *)
          cbv zeta.
          rewrite (errno_ret_in_below mmap_errnos addr) by
            first [ reflexivity
                  | alloc_top_bounds;
                      unfold two_pow_64 in *; lia ].
          rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl).
          cbn [andb]. reflexivity.
      - sys_unfold. cbv iota in H. inv_ok.
        + (* the environment errno *)
          cbv zeta.
          match goal with
          | |- context [errno_ret_in ?es (errno_ret ?e)] =>
              rewrite (errno_ret_in_intro es e) by assumption
          end.
          reflexivity.
        + (* -EEXIST *)
          cbv zeta. rewrite bv_eqb_refl, Bool.orb_true_r. reflexivity. }
    destruct (mmap_noreplace_rw_b prot flags off) eqn:Hnrr.
    2: { sys_unfold. inv_ok; discriminate. }
    cbv zeta in H. cbv zeta.
    destruct ((two_pow_64
               <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
      eqn:Hovf.
    { sys_unfold. inv_ok.
      cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
    apply get_model_bind_ok_inv in H. cbv beta in H.
    destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                      <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil.
    { sys_unfold. inv_ok; discriminate. }
    destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
    { sys_unfold. inv_ok.
      cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
    destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos.
    { sys_unfold. inv_ok; discriminate. }
    apply negb_false_iff, Z.leb_le in Hceil.
    pose proof (word_unsigned_range addr) as Haddr.
    pose proof (word_unsigned_range len) as Hlen.
    pose proof (page_round_up_Z_nonneg (bv_unsigned len) ltac:(lia)) as Hn.
    destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                   addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
      eqn:Hfree.
    - sys_unfold. cbv iota in H. inv_ok.
      + (* errno *)
        cbv zeta.
        match goal with
        | |- context [errno_ret_in ?es (errno_ret ?e)] =>
            rewrite (errno_ret_in_intro es e) by assumption
        end.
        reflexivity.
      + (* the grant *)
        cbv zeta.
        rewrite (errno_ret_in_below mmap_errnos addr) by
          first [ reflexivity
                | alloc_top_bounds;
                    unfold two_pow_64 in *; lia ].
        rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl).
        cbn [andb].
        match goal with
        | Hb : mmap_noreserve_backed_ok _ _ _ = true |- _ => rewrite Hb
        end.
        reflexivity.
    - sys_unfold. cbv iota in H. inv_ok.
      + (* the environment errno *)
        cbv zeta.
        match goal with
        | |- context [errno_ret_in ?es (errno_ret ?e)] =>
            rewrite (errno_ret_in_intro es e) by assumption
        end.
        reflexivity.
      + (* -EEXIST *)
        cbv zeta. rewrite bv_eqb_refl, Bool.orb_true_r. reflexivity. }
  cbv zeta in H. cbv zeta.
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hovf.
  { sys_unfold. inv_ok.
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
  apply get_model_bind_ok_inv in H. cbv beta in H.
  destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                    <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil.
  { sys_unfold. inv_ok; discriminate. }
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { sys_unfold. inv_ok.
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
  destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos.
  { sys_unfold. inv_ok; discriminate. }
  destruct (region_free (vm_reserved (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  2: { destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                      addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                      ) eqn:Hfresh.
       2: { destruct (region_free (vm_reserved (m_vmmaps m)) addr
                        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
              eqn:Hspan.
            2: { sys_unfold. cbv iota in H. inv_ok. }
            apply negb_false_iff, Z.leb_le in Hceil.
            pose proof (word_unsigned_range addr) as Haddr.
            pose proof (word_unsigned_range len) as Hlen.
            pose proof (page_round_up_Z_nonneg (bv_unsigned len)
                          ltac:(lia)) as Hn.
            sys_unfold. cbv iota in H. inv_ok.
            - (* errno, range preserved *)
              cbv zeta.
              match goal with
              | |- context [errno_ret_in ?es (errno_ret ?e)] =>
                  rewrite (errno_ret_in_intro es e) by assumption
              end.
              reflexivity.
            - (* spanning replacement *)
              cbv zeta.
              rewrite (errno_ret_in_below mmap_errnos addr) by
                first [ reflexivity
                      | alloc_top_bounds;
                          unfold two_pow_64 in *; lia ].
              rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl).
              match goal with
              | Hb : mmap_fixed_rw_span_budget_ok _ _ _ _ = true |- _ =>
                  rewrite Hb
              end.
              reflexivity.
            - (* errno, range destroyed *)
              cbv zeta.
              match goal with
              | |- context [errno_ret_in ?es (errno_ret ?e)] =>
                  rewrite (errno_ret_in_intro es e) by assumption
              end.
              cbv iota.
              rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
              reflexivity. }
       apply negb_false_iff, Z.leb_le in Hceil.
       pose proof (word_unsigned_range addr) as Haddr.
       pose proof (word_unsigned_range len) as Hlen.
       pose proof (page_round_up_Z_nonneg (bv_unsigned len) ltac:(lia)) as Hn.
       sys_unfold. cbv iota in H. inv_ok.
       - (* errno *)
         cbv zeta.
         match goal with
         | |- context [errno_ret_in ?es (errno_ret ?e)] =>
             rewrite (errno_ret_in_intro es e) by assumption
         end.
         reflexivity.
       - (* fresh grant *)
         cbv zeta.
         rewrite (errno_ret_in_below mmap_errnos addr) by
           first [ reflexivity
                 | alloc_top_bounds;
                     unfold two_pow_64 in *; lia ].
         rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl).
         cbn [andb].
         match goal with
         | Hb : mmap_noreserve_backed_ok _ _ _ = true |- _ => rewrite Hb
         end.
         reflexivity. }
  apply negb_false_iff, Z.leb_le in Hceil.
  pose proof (word_unsigned_range addr) as Haddr.
  pose proof (word_unsigned_range len) as Hlen.
  pose proof (page_round_up_Z_nonneg (bv_unsigned len) ltac:(lia)) as Hn.
  sys_unfold. cbv iota in H. inv_ok.
  - (* errno, range preserved *)
    cbv zeta.
    match goal with
    | |- context [errno_ret_in ?es (errno_ret ?e)] =>
        rewrite (errno_ret_in_intro es e) by assumption
    end.
    reflexivity.
  - (* success *)
    cbv zeta.
    rewrite (errno_ret_in_below mmap_errnos addr) by
      first [ reflexivity
            | alloc_top_bounds;
                unfold two_pow_64 in *; lia ].
    rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl).
    match goal with
    | Hb : mmap_fixed_rw_budget_ok _ _ _ _ = true |- _ => rewrite Hb
    end.
    reflexivity.
  - (* errno, range destroyed *)
    cbv zeta.
    match goal with
    | |- context [errno_ret_in ?es (errno_ret ?e)] =>
        rewrite (errno_ret_in_intro es e) by assumption
    end.
    cbv iota.
    rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
    reflexivity. }
  cbv zeta in H. cbv zeta.
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hovf.
  { sys_unfold. inv_ok.
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
  apply get_model_bind_ok_inv in H. cbv beta in H.
  destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                    <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil.
  { sys_unfold. inv_ok; discriminate. }
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { sys_unfold. inv_ok.
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
  destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos.
  { sys_unfold. inv_ok; discriminate. }
  destruct (region_free (vm_reserved (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  2: { destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                      addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
         eqn:Hfresh0.
       2: { destruct (region_free (vm_reserved (m_vmmaps m)) addr
                        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
              eqn:Hspan.
            2: { sys_unfold. cbv iota in H. inv_ok. }
            apply negb_false_iff, Z.leb_le in Hceil.
            pose proof (word_unsigned_range addr) as Haddr.
            pose proof (word_unsigned_range len) as Hlen.
            pose proof (page_round_up_Z_nonneg (bv_unsigned len)
                          ltac:(lia)) as Hn.
            sys_unfold. cbv iota in H. inv_ok.
            - (* errno, range preserved *)
              cbv zeta.
              match goal with
              | |- context [errno_ret_in ?es (errno_ret ?e)] =>
                  rewrite (errno_ret_in_intro es e) by assumption
              end.
              reflexivity.
            - (* spanning replacement *)
              cbv zeta.
              rewrite (errno_ret_in_below mmap_errnos addr) by
                first [ reflexivity
                      | alloc_top_bounds;
                          unfold two_pow_64 in *; lia ].
              rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl).
              cbn [andb]. reflexivity.
            - (* errno, range destroyed *)
              cbv zeta.
              match goal with
              | |- context [errno_ret_in ?es (errno_ret ?e)] =>
                  rewrite (errno_ret_in_intro es e) by assumption
              end.
              cbv iota.
              rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
              reflexivity. }
       apply negb_false_iff, Z.leb_le in Hceil.
       pose proof (word_unsigned_range addr) as Haddr.
       pose proof (word_unsigned_range len) as Hlen.
       pose proof (page_round_up_Z_nonneg (bv_unsigned len) ltac:(lia)) as Hn.
       sys_unfold. cbv iota in H. inv_ok.
       - (* errno *)
         cbv zeta.
         match goal with
         | |- context [errno_ret_in ?es (errno_ret ?e)] =>
             rewrite (errno_ret_in_intro es e) by assumption
         end.
         reflexivity.
       - (* fresh inaccessible reservation *)
         cbv zeta.
         rewrite (errno_ret_in_below mmap_errnos addr) by
           first [ reflexivity
                 | alloc_top_bounds;
                     unfold two_pow_64 in *; lia ].
         rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl).
         cbn [andb]. reflexivity. }
  apply negb_false_iff, Z.leb_le in Hceil.
  pose proof (word_unsigned_range addr) as Haddr.
  pose proof (word_unsigned_range len) as Hlen.
  pose proof (page_round_up_Z_nonneg (bv_unsigned len) ltac:(lia)) as Hn.
  sys_unfold. cbv iota in H. inv_ok.
  - (* errno, range preserved *)
    cbv zeta.
    match goal with
    | |- context [errno_ret_in ?es (errno_ret ?e)] =>
        rewrite (errno_ret_in_intro es e) by assumption
    end.
    reflexivity.
  - (* success *)
    cbv zeta.
    rewrite (errno_ret_in_below mmap_errnos addr) by
      first [ reflexivity
            | alloc_top_bounds;
                unfold two_pow_64 in *; lia ].
    rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl).
    reflexivity.
  - (* errno, range destroyed *)
    cbv zeta.
    match goal with
    | |- context [errno_ret_in ?es (errno_ret ?e)] =>
        rewrite (errno_ret_in_intro es e) by assumption
    end.
    cbv iota.
    rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
    reflexivity.
Qed.

Lemma check_mmap_complete_unmodeled : forall addr len prot flags fd off m i eff,
  mmap_spec addr len prot flags fd off i m Unmodeled ->
  check_mmap addr len prot flags fd off eff m = CheckUnmodeled.
Proof.
  intros addr len prot flags fd off m i eff H.
  unfold mmap_spec in H.
  unfold check_mmap.
  destruct (negb (mmap_off_aligned_b off)) eqn:Hoff.
  { destruct (mmap_pglen_ok_b len) eqn:Hpl;
      [sys_unfold; inv_ok; discriminate | reflexivity]. }
  destruct (negb (mmap_anon_b flags)) eqn:Hanon; [reflexivity|].
  destruct (w_is0 len) eqn:Hl.
  { destruct (mmap_plain_anon_b flags) eqn:Hpa;
      [sys_unfold; inv_ok; discriminate | reflexivity]. }
  destruct (mmap_modeled_b prot flags off) eqn:Hrw; cbn [negb].
  { destruct (mmap_noreserve_b flags); sys_unfold; cbv iota in H;
      inv_ok; discriminate. }
  destruct (mmap_noaccess_b prot flags off) eqn:Hnone.
  { destruct (mmap_noreserve_b flags); sys_unfold; cbv iota in H;
      inv_ok; discriminate. }
  destruct (mmap_fixed_noaccess_b prot flags off) eqn:Hfixed.
  2: {
  destruct (mmap_fixed_rw_b prot flags off) eqn:Hfrw.
  2: {
    (* MAP_FIXED_NOREPLACE: the spec declines only at the two gates the
       checker declines at; past them every resolution is an answer. *)
    destruct (mmap_noreplace_noaccess_b prot flags off) eqn:Hnrn.
    { cbv zeta in H. cbv zeta.
      destruct ((two_pow_64
                 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
        eqn:Hovf.
      { sys_unfold. cbv iota in H. inv_ok; discriminate. }
      apply bind_model_inv in H. cbv beta in H.
      destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                        <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil.
      { reflexivity. }
      destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
      { sys_unfold. cbv iota in H. inv_ok; discriminate. }
      destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos.
      { reflexivity. }
      destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                     addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
        eqn:Hfree; sys_unfold; cbv iota in H; inv_ok. }
    destruct (mmap_noreplace_rw_b prot flags off) eqn:Hnrr.
    2: reflexivity.
    cbv zeta in H. cbv zeta.
    destruct ((two_pow_64
               <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
      eqn:Hovf.
    { sys_unfold. cbv iota in H. inv_ok; discriminate. }
    apply bind_model_inv in H. cbv beta in H.
    destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                      <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil.
    { reflexivity. }
    destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
    { sys_unfold. cbv iota in H. inv_ok; discriminate. }
    destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos.
    { reflexivity. }
    destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                   addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
      eqn:Hfree; sys_unfold; cbv iota in H; inv_ok. }
  cbv zeta in H. cbv zeta.
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hovf.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  apply bind_model_inv in H. cbv beta in H.
  destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                    <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil.
  { reflexivity. }
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos.
  { reflexivity. }
  destruct (region_free (vm_reserved (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  2: { destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                      addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                      ) eqn:Hfresh.
       2: { destruct (region_free (vm_reserved (m_vmmaps m)) addr
                        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
              eqn:Hspan.
            2: reflexivity.
            sys_unfold. cbv iota in H. inv_ok. }
       sys_unfold. cbv iota in H. inv_ok. }
  sys_unfold. cbv iota in H. inv_ok. }
  cbv zeta in H. cbv zeta.
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hovf.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  apply bind_model_inv in H. cbv beta in H.
  destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                    <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil.
  { reflexivity. }
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos.
  { reflexivity. }
  destruct (region_free (vm_reserved (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  2: { destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                      addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
         eqn:Hfresh0.
       2: { destruct (region_free (vm_reserved (m_vmmaps m)) addr
                        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
              eqn:Hspan.
            2: reflexivity.
            sys_unfold. cbv iota in H. inv_ok. }
       sys_unfold. cbv iota in H. inv_ok. }
  sys_unfold. cbv iota in H. inv_ok.
Qed.

(* ---------------------------------------------------------------- munmap *)

Lemma check_munmap_sound_ok : forall addr len eff m m' evs i,
  check_munmap addr len eff m = CheckOk m' evs ->
  munmap_spec addr len i m (Ok eff m' evs).
Proof.
  intros addr len eff m m' evs i H.
  unfold check_munmap in H. unfold munmap_spec.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len)
    eqn:Hi.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  cbv zeta in H.
  destruct ((TASK_SIZE <? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z) eqn:Hbig.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_vmmaps_ok|]. cbv beta zeta. apply pure_ok. }
  destruct (map_has (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hhas.
  - destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
      [destruct zs as [|? ?]|]; try discriminate.
    destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
    eapply bind_ok0; [apply get_vmmaps_ok|]. cbv beta zeta.
    srw Hhas.
    destruct (errno_ret_in munmap_errnos r) eqn:He.
    + (* -ENOMEM, nothing unmapped *)
      destruct us as [|? ?]; [|discriminate].
      inversion H; clear H; subst.
      apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
      apply alt_l.
      eapply bind_ok0; [apply (choose_ok _ e); exact HIn|]. apply pure_ok.
    + (* the cut *)
      destruct (w_is0 r
                && listNN_eqb us [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
        eqn:HC; [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in HC as [Hr Hus].
      unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
      apply listNN_eqb_eq in Hus; subst us.
      apply alt_r.
      eapply bind_ok0; [apply modify_ok|].
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
  - destruct (munmap_free_ok (m_vmmaps m) addr
                (page_round_up_Z (bv_unsigned len)))
      eqn:Hfree.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_vmmaps_ok|]. cbv beta zeta.
      srw Hhas. srw Hfree. apply pure_ok. }
    destruct (munmap_cut_ok (m_vmmaps m) addr
                (page_round_up_Z (bv_unsigned len)))
      eqn:Hcut; [|discriminate].
    destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
      [destruct zs as [|? ?]|]; try discriminate.
    destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
    eapply bind_ok0; [apply get_vmmaps_ok|]. cbv beta zeta.
    srw Hhas. srw Hfree. srw Hcut.
    destruct (errno_ret_in munmap_errnos r) eqn:He.
    + (* -ENOMEM, nothing unmapped *)
      destruct us as [|? ?]; [|discriminate].
      inversion H; clear H; subst.
      apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
      apply alt_l.
      eapply bind_ok0; [apply (choose_ok _ e); exact HIn|]. apply pure_ok.
    + (* the cut *)
      destruct (w_is0 r && listNN_eqb us [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
        eqn:HC; [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in HC as [Hr Hus].
      unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
      apply listNN_eqb_eq in Hus; subst us.
      apply alt_r.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_munmap_sound_unmodeled : forall addr len eff m i,
  check_munmap addr len eff m = CheckUnmodeled -> munmap_spec addr len i m Unmodeled.
Proof.
  intros addr len eff m i H.
  unfold check_munmap in H. unfold munmap_spec.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len)
    eqn:Hi.
  { now apply check_ret_only_no_unmodeled in H. }
  cbv zeta in H.
  destruct ((TASK_SIZE <? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z) eqn:Hbig.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (map_has (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hhas.
  - exfalso. destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
      [destruct zs as [|? ?];
       [destruct cs as [|? ?];
        [destruct copyins as [|? ?];
         [destruct (errno_ret_in munmap_errnos r);
          [destruct us
          |destruct (w_is0 r
                   && listNN_eqb us
                        [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])]|]|]|]|];
      discriminate.
  - destruct (munmap_free_ok (m_vmmaps m) addr
                (page_round_up_Z (bv_unsigned len)))
      eqn:Hfree.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (munmap_cut_ok (m_vmmaps m) addr
                (page_round_up_Z (bv_unsigned len)))
      eqn:Hcut.
    { exfalso. destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
        [destruct zs as [|? ?];
         [destruct cs as [|? ?];
          [destruct copyins as [|? ?];
           [destruct (errno_ret_in munmap_errnos r);
            [destruct us
            |destruct (w_is0 r && listNN_eqb us [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])]|]|]|]|];
        discriminate. }
    eapply bind_unmodeled2; [apply get_vmmaps_ok|]. cbv beta zeta.
    srw Hhas. srw Hfree. srw Hcut. apply unmodeled_intro.
Qed.

Lemma check_munmap_complete_ok : forall addr len eff m m' evs i,
  munmap_spec addr len i m (Ok eff m' evs) ->
  check_munmap addr len eff m = CheckOk m' evs.
Proof.
  intros addr len eff m m' evs i H.
  unfold munmap_spec in H. unfold check_munmap.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len)
    eqn:Hi.
  { sys_unfold. inv_ok.
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
  sys_unfold. cbv iota zeta in H. cbv zeta. inv_ok.
  destruct ((TASK_SIZE <? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z) eqn:Hbig;
    hall Hbig; inv_ok.
  { cbn; rewrite bv_eqb_refl; reflexivity. }
  destruct (map_has (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hhas;
    hall Hhas; inv_ok.
  - (* -ENOMEM on the whole mapping *)
    cbv iota.
    match goal with
    | |- context [errno_ret_in ?es (errno_ret ?e)] =>
        rewrite (errno_ret_in_intro es e) by assumption
    end.
    reflexivity.
  - (* the cut *)
    cbv iota.
    replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false
      by reflexivity.
    unfold w_is0. rewrite bv_eqb_refl.
    rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - destruct (munmap_free_ok (m_vmmaps m) addr
                (page_round_up_Z (bv_unsigned len)))
      eqn:Hfree; hall Hfree; inv_ok.
    { cbv iota. cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
    destruct (munmap_cut_ok (m_vmmaps m) addr
                (page_round_up_Z (bv_unsigned len)))
      eqn:Hcut; hall Hcut; inv_ok.
    + (* -ENOMEM *)
      match goal with
      | |- context [errno_ret_in ?es (errno_ret ?e)] =>
          rewrite (errno_ret_in_intro es e) by assumption
      end.
      reflexivity.
    + (* the cut *)
      replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false
        by reflexivity.
      unfold w_is0. rewrite bv_eqb_refl.
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma check_munmap_complete_unmodeled : forall addr len m i eff,
  munmap_spec addr len i m Unmodeled -> check_munmap addr len eff m = CheckUnmodeled.
Proof.
  intros addr len m i eff H.
  unfold munmap_spec in H. unfold check_munmap.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len)
    eqn:Hi.
  { sys_unfold. inv_ok; discriminate. }
  sys_unfold. cbv iota zeta in H. cbv zeta. inv_ok.
  destruct ((TASK_SIZE <? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z) eqn:Hbig;
    hall Hbig; inv_ok; try discriminate.
  destruct (map_has (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hhas;
    hall Hhas; inv_ok; try discriminate.
  destruct (munmap_free_ok (m_vmmaps m) addr
              (page_round_up_Z (bv_unsigned len))) eqn:Hfree;
    hall Hfree; inv_ok; try discriminate.
  destruct (munmap_cut_ok (m_vmmaps m) addr
              (page_round_up_Z (bv_unsigned len))) eqn:Hcut;
    hall Hcut; inv_ok; try discriminate.
  reflexivity.
Qed.

(* --------------------------------------------------------------- mremap *)

(* -------------------------------------------------------------- mprotect *)

(* --------------------------------------------------------------- getrandom *)

(** The zero-byte arm proved once, for whichever return the range
    verdict allows beside the interrupted one. *)
