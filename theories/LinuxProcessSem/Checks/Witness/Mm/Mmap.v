(** * LinuxProcessSem.Checks.Witness.Mm.Mmap — the brk (214), mmap (222), munmap (215) witnesses, and their proofs

    Mirrors [Sys/Mm/Mmap.v], which answers to Linux [mm/mmap.c]: this
    file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude.

Definition brk_witness (req : word) (m : Model) : outcome SyscallEffect :=
  let h := m_vmmaps m in
  let r := vm_brk h in
  Ok (mkEffectU r [] (brk_zeros req r (vm_brk h))
                   (brk_unmaps r (vm_brk h)) [] [])
      (with_brk_next m req r) [].

Lemma brk_witness_ok : forall req i m, brk_spec req i m (brk_witness req m).
Proof.
  intros. unfold brk_spec, brk_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta zeta.
  eapply bind_step.
  { apply choose_ok. unfold brk_r_ok; cbv zeta.
    destruct (w_is0 req
              || Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps m)))).
    - apply bv_eqb_eq; reflexivity.
    - destruct (Z.ltb (bv_unsigned req) (bv_unsigned (vm_brk (m_vmmaps m)))).
      + rewrite (proj2 (bv_eqb_eq _ _) eq_refl), Bool.orb_true_r. reflexivity.
      + rewrite (proj2 (bv_eqb_eq _ _) eq_refl), Bool.orb_true_r, Bool.andb_true_l.
        unfold brk_grow_ok. now rewrite Z.ltb_irrefl, Bool.andb_false_r. }
  eapply bind_step; [apply modify_ok|]. apply pure_ok.
Qed.

(* =========================================================================
   mmap (222) / munmap (215) / mprotect (226)
   ========================================================================= *)

(** mmap witness: -EINVAL on a misaligned offset (with a length whose
    page-rounding does not wrap) or on a zero length in the plain
    anonymous shape, and -ENOMEM on a MAP_FIXED range whose
    page-rounded end leaves the address space; for the modeled shapes
    the environment-failure branch (errno 12), available regardless of
    the mapping ledger; [Unmodeled]
    on any unmodeled prot/flags/fd/off.  The MAP_FIXED branch admits
    three resolutions (see [Mmap.mmap_spec]); the witness keeps
    choosing the errno one that leaves the range in place, since it only
    has to be AN admissible outcome. *)

(** The MAP_FIXED arms over the vDSO pair ([Mmap.mmap_fixed_noaccess_vdso],
    [Mmap.mmap_fixed_rw_vdso]) carry the errno arm on every answering
    sub-case, and decline only a request that reaches the image. *)
Definition mmap_fixed_vdso_witness (addr : word) (nZ : Z) (m : Model)
    : outcome SyscallEffect :=
  let n := Z_to_bv 64 nZ in
  if vdso_split (m_vdso m) (bv_unsigned addr) (bv_unsigned addr + nZ)
  then ret_outcome (errno_ret witness_errno) m
  else if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n
  then ret_outcome (errno_ret witness_errno) m
  else if region_free (vm_reserved (m_vmmaps m)) addr n
  then ret_outcome (errno_ret witness_errno) m
  else Unmodeled.

Ltac mmap_fixed_vdso_witness_step :=
  cbv beta iota zeta;
  unfold mmap_fixed_noaccess_vdso, mmap_fixed_rw_vdso, mmap_fixed_vdso_witness;
  cbv zeta;
  match goal with
  | |- context [vdso_split ?v ?lo ?hi] => destruct (vdso_split v lo hi)
  end; cbv beta iota;
  [ apply alt_l; eapply bind_step; [apply errno_head_witness|]; apply pure_ok |];
  match goal with
  | |- context [region_free (?r ++ ?l) ?a ?n] => destruct (region_free (r ++ l) a n)
  end; cbv beta iota;
  [ apply alt_l; eapply bind_step; [apply errno_head_witness|]; apply pure_ok |];
  match goal with
  | |- context [region_free ?r ?a ?n] => destruct (region_free r a n)
  end; cbv beta iota;
  [ apply alt_l; eapply bind_step; [apply errno_head_witness|]; apply pure_ok
  | apply unmodeled_intro ].

Definition mmap_witness (addr len prot flags fd off : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (mmap_off_aligned_b off) then
    (if mmap_pglen_ok_b len then ret_outcome (errno_ret EINVAL) m
     else Unmodeled)
  else if negb (mmap_anon_b flags) then Unmodeled
  else if w_is0 len then
    (if mmap_plain_anon_b flags then ret_outcome (errno_ret EINVAL) m
     else Unmodeled)
  else if mmap_modeled_b prot flags off
  then ret_outcome (errno_ret witness_errno) m
  else if mmap_noaccess_b prot flags off
  then ret_outcome (errno_ret witness_errno) m
  else if mmap_fixed_noaccess_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z
    then ret_outcome (errno_ret ENOMEM) m
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then Unmodeled
    else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
    then ret_outcome (errno_ret EINVAL) m
    else if negb (0 <? bv_unsigned addr)%Z then Unmodeled
    else
      let n := Z_to_bv 64 nZ in
      if region_free (vm_reserved (m_vmmaps m)) addr n
         && map_contains (vm_maps (m_vmmaps m)) addr n
      then ret_outcome (errno_ret witness_errno) m
      else if vdso_meets (m_vdso m) (bv_unsigned addr) (bv_unsigned addr + nZ)
      then mmap_fixed_vdso_witness addr nZ m
      else if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                          addr n
      then ret_outcome (errno_ret witness_errno) m
      else if region_free (vm_reserved (m_vmmaps m)) addr n
      then ret_outcome (errno_ret witness_errno) m
      else Unmodeled
  else if mmap_fixed_rw_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z
    then ret_outcome (errno_ret ENOMEM) m
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then Unmodeled
    else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
    then ret_outcome (errno_ret EINVAL) m
    else if negb (0 <? bv_unsigned addr)%Z then Unmodeled
    else
      let n := Z_to_bv 64 nZ in
      if region_free (vm_reserved (m_vmmaps m)) addr n
         && map_contains (vm_maps (m_vmmaps m)) addr n
      then ret_outcome (errno_ret witness_errno) m
      else if vdso_meets (m_vdso m) (bv_unsigned addr) (bv_unsigned addr + nZ)
      then mmap_fixed_vdso_witness addr nZ m
      else if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                          addr n
      then ret_outcome (errno_ret witness_errno) m
      else if region_free (vm_reserved (m_vmmaps m)) addr n
      then ret_outcome (errno_ret witness_errno) m
      else Unmodeled
  (* MAP_FIXED_NOREPLACE, either prot: past the MAP_FIXED argument gate
     BOTH ledger sub-cases carry the errno arm — the free range as an
     ordinary grant, the occupied one beside its -EEXIST — so the witness
     needs no ledger test at all. *)
  else if mmap_noreplace_noaccess_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z
    then ret_outcome (errno_ret ENOMEM) m
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then Unmodeled
    else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
    then ret_outcome (errno_ret EINVAL) m
    else if negb (0 <? bv_unsigned addr)%Z then Unmodeled
    else ret_outcome (errno_ret witness_errno) m
  else if mmap_noreplace_rw_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z
    then ret_outcome (errno_ret ENOMEM) m
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then Unmodeled
    else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
    then ret_outcome (errno_ret EINVAL) m
    else if negb (0 <? bv_unsigned addr)%Z then Unmodeled
    else ret_outcome (errno_ret witness_errno) m
  else Unmodeled.

(** The NOREPLACE arms' witness, proved once for both prot words: the
    gate, then the errno arm of whichever [alt] the ledger selects. *)
Ltac mmap_noreplace_witness_step :=
  cbv zeta;
  match goal with
  | |- context [(two_pow_64 <=? bv_unsigned ?addr + page_round_up_Z (bv_unsigned ?len))%Z] =>
      destruct ((two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
        eqn:?Hovf; [apply pure_ok|]
  end;
  eapply bind_step; [apply get_model_ok|]; cbv beta zeta;
  match goal with
  | |- context [negb (bv_unsigned ?addr + page_round_up_Z (bv_unsigned ?len)
                       <=? alloc_top (m_vmmaps ?m))%Z] =>
      destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                        <=? alloc_top (m_vmmaps m))%Z) eqn:?Hceil;
        [apply unmodeled_intro|]
  end;
  match goal with
  | |- context [negb (Z.eqb (bv_unsigned ?addr mod page_size) 0)] =>
      destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:?Halign;
        [apply pure_ok|]
  end;
  match goal with
  | |- context [negb (0 <? bv_unsigned ?addr)%Z] =>
      destruct (negb (0 <? bv_unsigned addr)%Z) eqn:?Hpos;
        [apply unmodeled_intro|]
  end;
  match goal with
  | |- context [region_free ?l ?a ?n && ?rest] =>
      destruct (region_free l a n && rest)
  end;
  (apply alt_l; eapply bind_step; [apply errno_head_witness|]; apply pure_ok).

Lemma mmap_witness_ok : forall addr len prot flags fd off i m,
  mmap_spec addr len prot flags fd off i m
    (mmap_witness addr len prot flags fd off m).
Proof.
  intros. unfold mmap_spec, mmap_witness.
  destruct (negb (mmap_off_aligned_b off)) eqn:Hoff.
  { destruct (mmap_pglen_ok_b len) eqn:Hpl;
      [apply pure_ok|apply unmodeled_intro]. }
  destruct (negb (mmap_anon_b flags)) eqn:Hanon; [apply unmodeled_intro|].
  destruct (w_is0 len) eqn:Hl.
  { destruct (mmap_plain_anon_b flags) eqn:Hpa;
      [apply pure_ok|apply unmodeled_intro]. }
  destruct (mmap_modeled_b prot flags off) eqn:Hrw.
  { apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok. }
  destruct (mmap_noaccess_b prot flags off) eqn:Hnone.
  { apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok. }
  destruct (mmap_fixed_noaccess_b prot flags off) eqn:Hfixed.
  { cbv zeta.
    destruct ((two_pow_64
               <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
      eqn:Hovf; [apply pure_ok|].
    eapply bind_step; [apply get_model_ok|]. cbv beta zeta.
    destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                      <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil; [apply unmodeled_intro|].
    destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign;
      [apply pure_ok|].
    destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos;
      [apply unmodeled_intro|].
    destruct (region_free (vm_reserved (m_vmmaps m)) addr
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
              && map_contains (vm_maps (m_vmmaps m)) addr
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
    { apply alt_l. eapply bind_step; [apply errno_head_witness|].
      apply pure_ok. }
    destruct (vdso_meets (m_vdso m) (bv_unsigned addr)
                (bv_unsigned addr + page_round_up_Z (bv_unsigned len))) eqn:Hvd.
    { mmap_fixed_vdso_witness_step. }
    destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                   addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
      eqn:Hfresh0.
    { apply alt_l. eapply bind_step; [apply errno_head_witness|].
      apply pure_ok. }
    destruct (region_free (vm_reserved (m_vmmaps m)) addr
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
      eqn:Hspan.
    { apply alt_l. eapply bind_step; [apply errno_head_witness|].
      apply pure_ok. }
    apply unmodeled_intro. }
  destruct (mmap_fixed_rw_b prot flags off) eqn:Hfrw.
  2: { destruct (mmap_noreplace_noaccess_b prot flags off) eqn:Hnrn;
         [mmap_noreplace_witness_step|].
       destruct (mmap_noreplace_rw_b prot flags off) eqn:Hnrr;
         [mmap_noreplace_witness_step|apply unmodeled_intro]. }
  cbv zeta.
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hovf; [apply pure_ok|].
  eapply bind_step; [apply get_model_ok|]. cbv beta zeta.
  destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                    <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil; [apply unmodeled_intro|].
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign;
    [apply pure_ok|].
  destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos;
    [apply unmodeled_intro|].
  destruct (region_free (vm_reserved (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  { apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok. }
  destruct (vdso_meets (m_vdso m) (bv_unsigned addr)
              (bv_unsigned addr + page_round_up_Z (bv_unsigned len))) eqn:Hvd.
  { mmap_fixed_vdso_witness_step. }
  destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                 addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                 ) eqn:Hfresh.
  { apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok. }
  destruct (region_free (vm_reserved (m_vmmaps m)) addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hspan.
  { apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok. }
  apply unmodeled_intro.
Qed.

(** munmap witness: mirrors the spec's split — -EINVAL on a bad argument
    or a range leaving the user address space, the removal (with its
    unmap effect) on an exact recorded mapping, -EINVAL on a split of the
    vDSO pair, 0 with the covered ranges cleared on whole ranges of it,
    the no-op 0 on a free range below the stack band, and [Unmodeled]
    (fail closed) on a partial unmap, one touching the image, or a free
    range reaching into the band (see [Mmap.munmap_spec]). *)

Definition munmap_witness (addr len : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len
  then ret_outcome (errno_ret EINVAL) m
  else
    let h := m_vmmaps m in
    let nZ := page_round_up_Z (bv_unsigned len) in
    (* the range leaves the user address space: see [Mmap.munmap_spec] *)
    if (TASK_SIZE <? bv_unsigned addr + nZ)%Z then ret_outcome (errno_ret EINVAL) m
    else
    let n := Z_to_bv 64 nZ in
    if map_has (vm_maps h) addr n
    then Ok (mkEffectU (Z_to_bv 64 0) [] [] [(addr, n)] [] [])
            (with_mmap_destroyed addr n (mkVmMapsFull (vm_reserved h)
                            (map_remove (vm_maps h) addr)
                            (maps_subtract (vm_noaccess h)
                               (bv_unsigned addr)
                               (bv_unsigned addr + bv_unsigned n))
                            (vm_start_brk h) (vm_brk h) (vm_limit h)
      (vm_mmap_base h) (vm_init_sp h)) m) []
    else if vdso_split (m_vdso m) (bv_unsigned addr) (bv_unsigned addr + nZ)
    then ret_outcome (errno_ret EINVAL) m
    else if vdso_meets (m_vdso m) (bv_unsigned addr) (bv_unsigned addr + nZ)
    then (if munmap_vdso_ok h (m_vdso m) addr nZ
          then ret_outcome (Z_to_bv 64 0)
                 (with_vdso (vdso_cut (m_vdso m) (bv_unsigned addr)
                               (bv_unsigned addr + nZ)) m)
          else Unmodeled)
    else if munmap_free_ok h addr nZ
    then ret_outcome (Z_to_bv 64 0) m
    else Unmodeled.

Lemma munmap_witness_ok : forall addr len i m,
  munmap_spec addr len i m (munmap_witness addr len m).
Proof.
  intros. unfold munmap_spec, munmap_witness.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len) eqn:Hi;
    [apply pure_ok|].
  cbv zeta.
  destruct ((TASK_SIZE <? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z) eqn:Hbig.
  { eapply bind_step; [apply get_vmmaps_ok|]. cbv beta iota zeta.
    apply pure_ok. }
  destruct (map_has (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hhas.
  - eapply bind_step; [apply get_vmmaps_ok|]. cbv beta zeta.
    cbv iota. srw Hhas.
    eapply bind_step; [apply modify_ok|].
    eapply bind_step; [apply modify_ok|]. apply pure_ok.
  - eapply bind_step; [apply get_vmmaps_ok|]. cbv beta zeta.
    cbv iota. srw Hhas.
    eapply bind_step; [apply get_model_ok|]. cbv beta zeta.
    destruct (vdso_split (m_vdso m) (bv_unsigned addr)
                (bv_unsigned addr + page_round_up_Z (bv_unsigned len))) eqn:Hsp;
      cbv beta iota; [apply pure_ok|].
    destruct (vdso_meets (m_vdso m) (bv_unsigned addr)
                (bv_unsigned addr + page_round_up_Z (bv_unsigned len))) eqn:Hvd;
      cbv beta iota.
    { destruct (munmap_vdso_ok (m_vmmaps m) (m_vdso m) addr
                  (page_round_up_Z (bv_unsigned len))) eqn:Hok;
        cbv beta iota; [|apply unmodeled_intro].
      eapply bind_step; [apply modify_ok|]. apply pure_ok. }
    destruct (munmap_free_ok (m_vmmaps m) addr
                (page_round_up_Z (bv_unsigned len))) eqn:Hfree;
      cbv beta iota; [apply pure_ok|apply unmodeled_intro].
Qed.

(** mremap witness: deterministic -EINVAL for the modeled flag shape's
    misaligned address and zero/wrapping new size, [Unmodeled] for
    unsupported flags, the clone shape, and non-exact/protected source
    mappings.  Past those, an equal-size call has no injectable failure at
    all (Linux cannot fail one for lack of memory — see [mremap_spec]), so
    the witness is its deterministic success; every resizing call still has
    the always-available ENOMEM branch. *)

(** mprotect witness: the argument gates first, in Linux's order — the
    PROT_GROWSDOWN|PROT_GROWSUP conflict and a misaligned address are
    -EINVAL, a zero [len] is 0 and a page-rounded end past 2^64 is -ENOMEM,
    both for any [prot] that got past them (see
    [Mprotect.mprotect_spec]).  Past those, the no-op success for the one
    modeled [prot] (rw — the permissions the model's memory already has),
    and [Unmodeled] (fail closed) for every other, PROT_EXEC above all. *)

(* =========================================================================
   getrandom (278) — witness: the full delivery of a small request,
   environment failure (EINTR) for every other, or [Unmodeled] on
   unmodeled flags / an unwritable destination; readlinkat (78) —
   deterministic -EINVAL under AT_FDCWD, [Unmodeled] on any other dirfd
   ========================================================================= *)

(** getrandom's witness: [Unmodeled] on unmodeled flags (GRND_RANDOM or
    unknown bits — fail closed, but never stuck); the full delivery for
    a nonzero request of at most [Random.getrandom_small_max] bytes,
    which has no errno branch; otherwise the always-available errno
    branch — EINTR, the head of [getrandom_errnos].  The >= 1 lower
    bound only constrains a large request's success branch, so the
    errno witness is unaffected by it. *)
