(** * LinuxProcessSem.Checks.Sys.Prelude — the checkers' shared helpers, reflections and tactics

    Shared infrastructure for the checkers below it: this one mirrors no
    kernel source, and holds nothing syscall-specific.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.

Inductive check_result :=
  | CheckOk (m : Model) (evs : list event)
  | CheckReject
  | CheckUnmodeled.

(* =========================================================================
   Boolean helpers and their reflections
   ========================================================================= *)

Lemma bv_eqb_refl : forall (n : N) (a : bv n), bv_eqb a a = true.
Proof. intros n a. apply bv_eqb_eq. reflexivity. Qed.

(** Byte-list equality; bytes are [bv 8]. *)

Fixpoint listN_eqb (l1 l2 : list byte) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: r1, b :: r2 => bv_eqb a b && listN_eqb r1 r2
  | _, _ => false
  end.

Lemma listN_eqb_eq : forall l1 l2, listN_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|a r1 IH]; destruct l2 as [|b r2]; cbn;
    try (split; congruence).
  rewrite Bool.andb_true_iff, bv_eqb_eq, IH.
  split; [intros [-> ->]; auto | intro H; inversion H; auto].
Qed.

(** Equality of zero-range / unmap-range lists ([eff_zeros],
    [eff_unmaps]). *)

Fixpoint listNN_eqb (l1 l2 : list (word * word)) : bool :=
  match l1, l2 with
  | [], [] => true
  | (a1, n1) :: r1, (a2, n2) :: r2 =>
      bv_eqb a1 a2 && bv_eqb n1 n2 && listNN_eqb r1 r2
  | _, _ => false
  end.

Lemma listNN_eqb_eq : forall l1 l2, listNN_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|[a1 n1] r1 IH]; destruct l2 as [|[a2 n2] r2]; cbn;
    try (split; congruence).
  rewrite !Bool.andb_true_iff, !bv_eqb_eq, IH.
  split; [intros [[-> ->] ->]; auto | intro H; inversion H; auto].
Qed.

(** Equality for the symbolic pre-effect copy ledger. *)

Definition copy_eqb (c1 c2 : MemCopy) : bool :=
  bv_eqb (copy_src c1) (copy_src c2)
  && bv_eqb (copy_dst c1) (copy_dst c2)
  && bv_eqb (copy_len c1) (copy_len c2).

Fixpoint listCopy_eqb (l1 l2 : list MemCopy) : bool :=
  match l1, l2 with
  | [], [] => true
  | c1 :: r1, c2 :: r2 => copy_eqb c1 c2 && listCopy_eqb r1 r2
  | _, _ => false
  end.

Lemma copy_eqb_eq : forall c1 c2, copy_eqb c1 c2 = true <-> c1 = c2.
Proof.
  intros [s1 d1 n1] [s2 d2 n2]. unfold copy_eqb. cbn.
  rewrite !Bool.andb_true_iff, !bv_eqb_eq.
  split; [intros [[-> ->] ->]; reflexivity|intro H; inversion H; auto].
Qed.

Lemma listCopy_eqb_eq : forall l1 l2,
  listCopy_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|c1 r1 IH]; destruct l2 as [|c2 r2]; cbn;
    try (split; congruence).
  rewrite Bool.andb_true_iff, copy_eqb_eq, IH.
  split; [intros [-> ->]; reflexivity|intro H; inversion H; auto].
Qed.

(** Equality for syscall write lists: addresses plus their byte strings. *)

Fixpoint writes_eqb (l1 l2 : list (word * list byte)) : bool :=
  match l1, l2 with
  | [], [] => true
  | (a1, bs1) :: r1, (a2, bs2) :: r2 =>
      bv_eqb a1 a2 && listN_eqb bs1 bs2 && writes_eqb r1 r2
  | _, _ => false
  end.

Lemma writes_eqb_eq : forall l1 l2, writes_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|[a1 bs1] r1 IH]; destruct l2 as [|[a2 bs2] r2]; cbn;
    try (split; congruence).
  rewrite !Bool.andb_true_iff, bv_eqb_eq, listN_eqb_eq, IH.
  split; [intros [[-> ->] ->]; auto | intro H; inversion H; auto].
Qed.

(** Range of a 64-bit word's unsigned value, with the modulus exposed as
    the [two_pow_64] constant. *)

Lemma word_unsigned_range : forall (w : word),
  (0 <= bv_unsigned w < two_pow_64)%Z.
Proof.
  intros w. pose proof (bv_unsigned_in_range _ w) as H.
  unfold two_pow_64. unfold bv_modulus in H.
  change (Z.of_N 64) with 64%Z in H. exact H.
Qed.

(** The unsigned value of an in-range errno return. *)

Lemma errno_ret_unsigned : forall e,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  bv_unsigned (errno_ret e) = (two_pow_64 - e)%Z.
Proof.
  intros e H1 H2. unfold errno_ret, two_pow_64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (Z.of_N 64) with 64%Z.
  replace (- e)%Z with (2 ^ 64 - e + (-1) * 2 ^ 64)%Z by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(** An error-encoded return value is exactly [errno_ret e] for an errno
    in [1,4095]. *)

Lemma errno_ret_error_b : forall e,
  (1 <= e)%Z -> (e <= 4095)%Z -> addr_is_error_b (errno_ret e) = true.
Proof.
  intros e H1 H2. unfold addr_is_error_b.
  rewrite (errno_ret_unsigned e H1 H2). unfold two_pow_64.
  apply Z.ltb_lt. lia.
Qed.

Lemma addr_is_error_b_errno : forall r,
  addr_is_error_b r = true ->
  exists e, (1 <= e)%Z /\ (e <= 4095)%Z /\ r = errno_ret e.
Proof.
  intros r H. unfold addr_is_error_b in H.
  apply Z.ltb_lt in H. unfold two_pow_64 in H.
  pose proof (word_unsigned_range r) as Hr. unfold two_pow_64 in Hr.
  exists (2 ^ 64 - bv_unsigned r)%Z.
  split; [lia|]. split; [lia|].
  apply bv_eq. rewrite errno_ret_unsigned by lia.
  unfold two_pow_64. lia.
Qed.

(** The acceptor side of [Syscall.errno_any]: an error-encoded return
    other than -EINTR. *)
Definition errno_any_b (r : word) : bool :=
  addr_is_error_b r && negb (bv_eqb r (errno_ret EINTR)).

Lemma errno_any_b_errno : forall r,
  errno_any_b r = true ->
  exists e, ((1 <= e <= 4095)%Z /\ e <> EINTR) /\ r = errno_ret e.
Proof.
  intros r H. unfold errno_any_b in H.
  apply andb_true_iff in H as [He Hn].
  apply addr_is_error_b_errno in He. destruct He as (e & H1 & H2 & ->).
  exists e. split; [|reflexivity]. split; [lia|].
  intros ->. rewrite bv_eqb_refl in Hn. discriminate.
Qed.

Lemma errno_any_b_ret : forall e,
  (1 <= e <= 4095)%Z /\ e <> EINTR -> errno_any_b (errno_ret e) = true.
Proof.
  intros e [[H1 H2] Hn]. unfold errno_any_b.
  rewrite errno_ret_error_b by lia. cbn [andb].
  destruct (bv_eqb (errno_ret e) (errno_ret EINTR)) eqn:Hq; [|reflexivity].
  apply bv_eqb_eq in Hq. apply (f_equal bv_unsigned) in Hq.
  rewrite !errno_ret_unsigned in Hq by (unfold EINTR; lia).
  exfalso. apply Hn. lia.
Qed.

(** Does [r] encode [-e] for some errno in the injectable set [es]? *)

Definition errno_ret_in (es : list Z) (r : word) : bool :=
  existsb (fun e => bv_eqb r (errno_ret e)) es.

Lemma errno_ret_in_true : forall es r,
  errno_ret_in es r = true <-> exists e, In e es /\ r = errno_ret e.
Proof.
  intros es r. unfold errno_ret_in. rewrite existsb_exists.
  split; intros (e & H1 & H2); exists e;
    [rewrite bv_eqb_eq in H2 | rewrite bv_eqb_eq]; auto.
Qed.

Lemma errno_ret_in_intro : forall es e, In e es ->
  errno_ret_in es (errno_ret e) = true.
Proof. intros. apply errno_ret_in_true. eauto. Qed.

(** Every injectable set holds genuine errnos (in [1, 4095]). *)

Definition errnos_ok (es : list Z) : bool :=
  forallb (fun e => (1 <=? e)%Z && (e <=? 4095)%Z) es.

Lemma errnos_ok_range : forall es e,
  errnos_ok es = true -> In e es -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof.
  induction es as [|x es IH]; intros e Hok HIn; [destruct HIn|].
  cbn in Hok. apply andb_true_iff in Hok as [Hx Hok].
  apply andb_true_iff in Hx as [H1 H2].
  destruct HIn as [-> | HIn];
    [ split; apply Z.leb_le; assumption
    | apply IH; assumption ].
Qed.

(** A value far below the error-encoding window (in particular any
    fd < 2^31, or any grant address below [alloc_top]) never
    matches an injectable errno. *)

Lemma errno_ret_in_below : forall es r,
  errnos_ok es = true -> (bv_unsigned r <= two_pow_64 - 4096)%Z ->
  errno_ret_in es r = false.
Proof.
  induction es as [|e es IH]; intros r Hok Hr; [reflexivity|].
  cbn in Hok. apply andb_true_iff in Hok as [He Hok].
  apply andb_true_iff in He as [He1 He2].
  apply Z.leb_le in He1. apply Z.leb_le in He2.
  unfold errno_ret_in in *. cbn [existsb].
  rewrite IH by assumption. rewrite Bool.orb_false_r.
  unfold bv_eqb. apply Z.eqb_neq.
  rewrite errno_ret_unsigned by assumption.
  unfold two_pow_64 in *. lia.
Qed.

Lemma errno_ret_in_fd : forall es fd,
  errnos_ok es = true -> (bv_unsigned fd < 2 ^ 31)%Z ->
  errno_ret_in es fd = false.
Proof.
  intros es fd Hok Hfd. apply errno_ret_in_below; [exact Hok|].
  unfold two_pow_64. lia.
Qed.

(** Is [buf, buf+n) writable-mapped?  Decides the delivered-prefix
    writability side condition of [read_spec]. *)

Definition wmem_ok (i : SyscallInput) (buf n : word) : bool :=
  match read_bytes_map (in_wmem i) buf n with
  | Some _ => true
  | None => false
  end.

Lemma wmem_ok_true : forall i buf n,
  wmem_ok i buf n = true <-> read_bytes_map (in_wmem i) buf n <> None.
Proof.
  intros. unfold wmem_ok.
  destruct (read_bytes_map (in_wmem i) buf n); split; congruence.
Qed.

(** A prefix of a readable range is readable (and reads the prefix). *)

Lemma read_bytes_aux_prefix : forall k n mp a w,
  (k <= n)%nat -> read_bytes_aux mp a n = Some w ->
  read_bytes_aux mp a k = Some (firstn k w).
Proof.
  induction k as [|k IH]; intros n mp a w Hk Hw; [reflexivity|].
  destruct n as [|n]; [lia|].
  cbn in Hw. destruct (mp a) as [b|] eqn:Hb; [|discriminate].
  destruct (read_bytes_aux mp (a + 1) n) as [r|] eqn:Hr; [|discriminate].
  inversion Hw; subst w.
  cbn. rewrite Hb. rewrite (IH n mp (a + 1) r ltac:(lia) Hr). reflexivity.
Qed.

Lemma read_bytes_map_prefix : forall mp a len k w,
  (bv_unsigned k <= bv_unsigned len)%Z -> read_bytes_map mp a len = Some w ->
  read_bytes_map mp a k = Some (firstn (word_to_nat k) w).
Proof.
  intros mp a len k w Hk Hw. rewrite read_bytes_map_eq in *.
  unfold word_to_nat in *.
  apply read_bytes_aux_prefix with (n := Z.to_nat (bv_unsigned len));
    [lia | assumption].
Qed.

(** Full-range writability implies prefix writability — lets callers
    that established the whole [count] writable keep working. *)

Lemma wmem_ok_of_full : forall i buf count w k,
  read_bytes_map (in_wmem i) buf count = Some w ->
  (bv_unsigned k <= bv_unsigned count)%Z ->
  wmem_ok i buf k = true.
Proof.
  intros i buf count w k Hw Hk. unfold wmem_ok.
  erewrite read_bytes_map_prefix; eauto.
Qed.

(** Full-readability facts: when the whole range reads, the readable
    prefix IS the whole buffer, of the full length. *)

Lemma read_bytes_aux_length : forall mp k a w,
  read_bytes_aux mp a k = Some w -> length w = k.
Proof.
  intros mp k; induction k as [|k IH]; intros a w Hw; cbn in Hw.
  - inversion Hw. reflexivity.
  - destruct (mp a); [|discriminate].
    destruct (read_bytes_aux mp (a + 1) k) eqn:Hr; [|discriminate].
    inversion Hw; subst. cbn. now rewrite (IH _ _ Hr).
Qed.

Lemma read_bytes_map_length : forall mp a len w,
  read_bytes_map mp a len = Some w -> Z.of_nat (length w) = bv_unsigned len.
Proof.
  intros mp a len w Hw. rewrite read_bytes_map_eq in Hw.
  unfold word_to_nat in Hw.
  rewrite (read_bytes_aux_length _ _ _ _ Hw).
  pose proof (word_unsigned_range len). lia.
Qed.

Lemma readable_bytes_aux_full : forall mp k a w,
  read_bytes_aux mp a k = Some w -> readable_bytes_aux mp a k = w.
Proof.
  intros mp k; induction k as [|k IH]; intros a w Hw; cbn in *.
  - now inversion Hw.
  - destruct (mp a); [|discriminate].
    destruct (read_bytes_aux mp (a + 1) k) eqn:Hr; [|discriminate].
    inversion Hw; subst. now rewrite (IH _ _ Hr).
Qed.

Lemma readable_bytes_full : forall mp a len w,
  read_bytes_map mp a len = Some w -> readable_bytes mp a len = w.
Proof.
  intros. rewrite read_bytes_map_eq in *. rewrite readable_bytes_eq.
  now apply readable_bytes_aux_full.
Qed.

(** A SHORTER walk over a range that reads whole is that range's prefix.
    This is what a write's source is when the kernel's [MAX_RW_COUNT]
    clamp bites: [Uaccess.write_source] walks the clamped count, so a
    proof holding the whole named range still knows exactly which bytes
    the transfer sees, without a bound on the count. *)
Lemma readable_bytes_aux_prefix : forall mp n k a w,
  read_bytes_aux mp a n = Some w ->
  (k <= n)%nat ->
  readable_bytes_aux mp a k = firstn k w.
Proof.
  intros mp n; induction n as [|n IH]; intros k a w Hw Hk; cbn in Hw.
  - inversion Hw; subst. destruct k; [reflexivity|lia].
  - destruct (mp a) as [b|] eqn:Hb; [|discriminate].
    destruct (read_bytes_aux mp (a + 1) n) as [r|] eqn:Hr; [|discriminate].
    inversion Hw; subst w.
    destruct k as [|k]; [reflexivity|].
    cbn [readable_bytes_aux firstn]. rewrite Hb.
    f_equal. apply (IH k (a + 1)%bv r Hr). lia.
Qed.

Lemma write_source_prefix : forall mp a len w,
  read_bytes_map mp a len = Some w ->
  write_source mp a len = firstn (Z.to_nat (rw_count_clamp len)) w.
Proof.
  intros mp a len w H. rewrite read_bytes_map_eq in H.
  unfold write_source. rewrite readable_bytes_eq.
  unfold word_to_nat at 1. rewrite rw_count_clamp_word.
  pose proof (rw_count_clamp_range len) as Hr.
  apply (readable_bytes_aux_prefix mp (word_to_nat len) _ _ _ H).
  unfold word_to_nat, rw_count_clamp in *. lia.
Qed.

(** A zero-length destination always reads: [read_spec]'s file branch can
    only reach its unwritable case with a NONEMPTY delivered prefix. *)

Lemma read_bytes_map_nil : forall mp a,
  read_bytes_map mp a (len_word (@nil byte)) = Some [].
Proof.
  intros mp a. rewrite read_bytes_map_eq.
  replace (word_to_nat (len_word (@nil byte))) with 0%nat
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

(** The EFAULT gate is off when the readable prefix has the full
    (arbitrary) length: it reduces to [negb b && b]. *)

Lemma negb_andb_diag : forall b, negb b && b = false.
Proof. destruct b; reflexivity. Qed.

(** A fully readable iovec sequence's gatherable prefix is the whole
    flattening... *)

Lemma gather_prefix_full : forall mp iovs bs,
  gather_iovecs mp iovs = Some bs -> gather_prefix mp iovs = bs.
Proof.
  induction iovs as [|[base len] r IH]; intros bs Hg; cbn in *.
  - now inversion Hg.
  - destruct (read_bytes_map mp base len) as [w|] eqn:Hw; [|discriminate].
    destruct (gather_iovecs mp r) as [rest|] eqn:Hr; [|discriminate].
    inversion Hg; subst.
    rewrite (readable_bytes_full _ _ _ _ Hw).
    rewrite (read_bytes_map_length _ _ _ _ Hw), Z.eqb_refl.
    now rewrite (IH _ eq_refl).
Qed.

(** ...of the full requested length. *)

Lemma gather_iovecs_length : forall mp iovs bs,
  gather_iovecs mp iovs = Some bs -> Z.of_nat (length bs) = iovs_total iovs.
Proof.
  induction iovs as [|[base len] r IH]; intros bs Hg; cbn in *.
  - now inversion Hg.
  - destruct (read_bytes_map mp base len) as [w|] eqn:Hw; [|discriminate].
    destruct (gather_iovecs mp r) as [rest|] eqn:Hr; [|discriminate].
    inversion Hg; subst.
    rewrite length_app, Nat2Z.inj_add.
    rewrite (read_bytes_map_length _ _ _ _ Hw), (IH _ eq_refl). reflexivity.
Qed.

(** [alloc_fd] scans at most 4096 candidates starting at 0, so its result
    is at most 4096 — far below the error-encoding range
    [2^64-4095, 2^64), so a successful open's return is never confused
    with an errno. *)

Definition check_ret_only (eff : SyscallEffect) (r : word) (m' : Model)
    (evs : list event) : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if bv_eqb ret r then CheckOk m' evs else CheckReject
  | _ => CheckReject
  end.

Fixpoint access_ranges_eqb (xs ys : list (word * nat)) : bool :=
  match xs, ys with
  | [], [] => true
  | (a, n) :: xs', (b, k) :: ys' =>
      bv_eqb a b && Nat.eqb n k && access_ranges_eqb xs' ys'
  | _, _ => false
  end.

Lemma access_ranges_eqb_eq : forall xs ys,
  access_ranges_eqb xs ys = true <-> xs = ys.
Proof.
  induction xs as [|[a n] xs IH]; intros [|[b k] ys]; cbn; try easy.
  rewrite !andb_true_iff, bv_eqb_eq, Nat.eqb_eq, IH.
  split; [intros ((-> & ->) & ->); reflexivity|intros H; inversion H; auto].
Qed.

Lemma access_ranges_eqb_refl : forall xs, access_ranges_eqb xs xs = true.
Proof. intros. now apply access_ranges_eqb_eq. Qed.

Definition clear_copyins (eff : SyscallEffect) : SyscallEffect :=
  with_copyins [] eff.

Definition check_ret_only_copyins (reads : list (word * nat))
    (eff : SyscallEffect) (r : word) (m' : Model) (evs : list event)
    : check_result :=
  match check_ret_only (clear_copyins eff) r m' evs with
  | CheckOk m'' evs' =>
      if access_ranges_eqb (eff_copyins eff) reads
      then CheckOk m'' evs'
      else CheckReject
  | result => result
  end.

Definition check_copyins (reads : list (word * nat)) (eff : SyscallEffect)
    (result : check_result) : check_result :=
  if access_ranges_eqb (eff_copyins eff) reads then result else CheckReject.

Definition strip_copyin_prefix (reads : list (word * nat))
    (eff : SyscallEffect) : SyscallEffect :=
  with_copyins (skipn (length reads) (eff_copyins eff)) eff.

Definition check_copyin_prefix (reads : list (word * nat))
    (eff : SyscallEffect) (result : check_result) : check_result :=
  match result with
  | CheckUnmodeled => CheckUnmodeled
  | result' =>
      if access_ranges_eqb (firstn (length reads) (eff_copyins eff)) reads
      then result'
      else CheckReject
  end.

(* -------------------------------------------------- pathname copy-ins

   A spec whose body performs a single pathname read and no later
   copy-in records that one range with [Syscall.record_copyins].  These
   relate such a spec to its checker: the checker decides the body
   against the effect with its ledger CLEARED, then requires the claimed
   ledger to equal exactly that range.  [CheckUnmodeled] passes straight
   through — the model left the modeled surface, so it makes no claim
   about what was copied.  Two consumers: [Fs.Open.check_openat]
   and [Fs.Namei.check_unlinkat]. *)

Definition check_copyins_after (reads : list (word * nat))
    (eff : SyscallEffect) (result : check_result) : check_result :=
  match result with
  | CheckUnmodeled => CheckUnmodeled
  | result' => check_copyins reads eff result'
  end.

Lemma check_copyins_after_ok_iff : forall reads eff result m evs,
  check_copyins_after reads eff result = CheckOk m evs <->
  eff_copyins eff = reads /\ result = CheckOk m evs.
Proof.
  intros reads eff [m' evs'| |] m evs.
  - unfold check_copyins_after, check_copyins.
    destruct (access_ranges_eqb (eff_copyins eff) reads) eqn:Hreads.
    + apply access_ranges_eqb_eq in Hreads. subst.
      split; [intro H; inversion H; auto|intros (_ & H); exact H].
    + split; [discriminate|intros (H & _)].
      rewrite H in Hreads.
      rewrite (proj2 (access_ranges_eqb_eq reads reads) eq_refl) in Hreads.
      discriminate.
  - unfold check_copyins_after, check_copyins.
    destruct (access_ranges_eqb (eff_copyins eff) reads); split.
    all: try discriminate.
    all: intros (_ & H); discriminate.
  - unfold check_copyins_after.
    split; [discriminate|intros (_ & H); discriminate].
Qed.

Lemma check_copyins_after_unmodeled : forall reads eff result,
  check_copyins_after reads eff result = CheckUnmodeled ->
  result = CheckUnmodeled.
Proof.
  intros reads eff [m evs| |] H; unfold check_copyins_after in H.
  - unfold check_copyins in H.
    destruct (access_ranges_eqb (eff_copyins eff) reads); discriminate.
  - unfold check_copyins in H.
    destruct (access_ranges_eqb (eff_copyins eff) reads); discriminate.
  - reflexivity.
Qed.

Lemma record_copyins_clear_ok : forall reads spec i m eff m' evs,
  eff_copyins eff = reads ->
  spec i m (Ok (clear_copyins eff) m' evs) ->
  record_copyins reads spec i m (Ok eff m' evs).
Proof.
  intros reads spec i m eff m' evs Hreads Hspec.
  replace eff with (with_copyins reads (clear_copyins eff)).
  - apply record_copyins_ok_empty; [reflexivity|exact Hspec].
  - destruct eff as [ret ws zs us cs copyins].
    cbn in Hreads |- *. now subst copyins.
Qed.

Lemma input_bind_ok_inv {A : Type} : forall (k : SyscallInput -> Sys A)
    i m x m' evs,
  bind input k i m (Ok x m' evs) -> k i i m (Ok x m' evs).
Proof.
  intros k i m x m' evs H.
  unfold bind, input in H. cbv beta iota in H.
  destruct H as (i' & m1 & evs1 & evs2 & Hinput & Hk & Hevs).
  inversion Hinput; clear Hinput; subst.
  exact Hk.
Qed.

Lemma record_copyins_ok_inv : forall reads spec i m eff m' evs,
  record_copyins reads spec i m (Ok eff m' evs) ->
  exists core,
    spec i m (Ok core m' evs) /\
    eff = with_copyins (reads ++ eff_copyins core) core.
Proof.
  intros reads spec i m eff m' evs H.
  unfold record_copyins, bind, pure in H. cbv beta iota in H.
  destruct H as (core & m1 & evs1 & evs2 & Hcore & Hpure & Hevs).
  inversion Hpure; clear Hpure; subst.
  exists core. split; [rewrite app_nil_r; exact Hcore|reflexivity].
Qed.

Lemma input_bind_unmodeled_inv {A : Type} :
    forall (k : SyscallInput -> Sys A) i m,
  bind input k i m Unmodeled -> k i i m Unmodeled.
Proof.
  intros k i m H. unfold bind, input in H. cbv beta iota in H.
  destruct H as [Hinput | (i' & m1 & evs1 & Hinput & Hk)].
  - discriminate Hinput.
  - inversion Hinput; clear Hinput; subst. exact Hk.
Qed.

(** The same two, for the [get_model] a spec reads right after its
    input.  [Fs.Namei.unlinkat_spec] opens with both because its flag
    test precedes the copy-in it records, so the two binds sit outside
    the [record_copyins] rather than inside it. *)
Lemma get_model_bind_ok_inv {A : Type} : forall (k : Model -> Sys A)
    i m x m' evs,
  bind get_model k i m (Ok x m' evs) -> k m i m (Ok x m' evs).
Proof.
  intros k i m x m' evs H.
  unfold bind, get_model in H. cbv beta iota in H.
  destruct H as (m0 & m1 & evs1 & evs2 & Hget & Hk & Hevs).
  inversion Hget; clear Hget; subst.
  exact Hk.
Qed.

Lemma get_model_bind_unmodeled_inv {A : Type} :
    forall (k : Model -> Sys A) i m,
  bind get_model k i m Unmodeled -> k m i m Unmodeled.
Proof.
  intros k i m H. unfold bind, get_model in H. cbv beta iota in H.
  destruct H as [Hget | (m0 & m1 & evs1 & Hget & Hk)].
  - discriminate Hget.
  - inversion Hget; clear Hget; subst. exact Hk.
Qed.

Lemma record_copyins_unmodeled_inv : forall reads spec i m,
  record_copyins reads spec i m Unmodeled -> spec i m Unmodeled.
Proof.
  intros reads spec i m H. unfold record_copyins, bind, pure in H.
  cbv beta iota in H.
  destruct H as [Hcore | (core & m1 & evs1 & Hcore & Hpure)].
  - exact Hcore.
  - discriminate Hpure.
Qed.


(** Peel an [i <- input ;; m <- get_model ;; ...] prologue.  Both
    readers step to the syscall's own model and input emitting nothing,
    so an outcome of the pair is an outcome of the body — and unlike
    [inv_ok], this keeps the body's hypothesis under a name a later step
    can still pass to another lemma.  Both [recvfrom_spec] and
    [socketpair_spec] open this way, in this order. *)
Lemma bind_input_model_inv {A} :
  forall (k : SyscallInput -> Model -> Sys A) i m o,
  bind input (fun i0 => bind get_model (fun m0 => k i0 m0)) i m o ->
  k i m i m o.
Proof.
  intros k i m o H. destruct o as [y m2 evs|].
  - destruct H as (i0 & m1 & evs1 & evs2 & Hin & H & ->).
    unfold input in Hin. injection Hin as -> -> ->.
    destruct H as (m0 & m3 & evs3 & evs4 & Hgm & H & ->).
    unfold get_model in Hgm. injection Hgm as -> -> ->.
    exact H.
  - destruct H as [Hin | (i0 & m1 & evs1 & Hin & H)].
    + unfold input in Hin. discriminate.
    + unfold input in Hin. injection Hin as -> -> ->.
      destruct H as [Hgm | (m0 & m3 & evs3 & Hgm & H)].
      * unfold get_model in Hgm. discriminate.
      * unfold get_model in Hgm. injection Hgm as -> -> ->. exact H.
Qed.

(** The one-reader case of the same peel, for an arm that opens with
    [m <- get_model ;; ...] alone. *)
Lemma bind_model_inv {A} : forall (k : Model -> Sys A) i m o,
  bind get_model k i m o -> k m i m o.
Proof.
  intros k i m o H. destruct o as [y m2 evs|].
  - destruct H as (m0 & m1 & evs1 & evs2 & Hgm & H & ->).
    unfold get_model in Hgm. injection Hgm as -> -> ->. exact H.
  - destruct H as [Hgm | (m0 & m1 & evs1 & Hgm & H)].
    + unfold get_model in Hgm. discriminate.
    + unfold get_model in Hgm. injection Hgm as -> -> ->. exact H.
Qed.

(** [Uaccess.access_ok_zero] as an acceptor: when the kernel moved no
    bytes, the range verdict is all that is left, so either the arm's
    own zero answer stands, or the only admissible return is -EFAULT, or
    the model declines. *)

Definition eff_is_errno (code : Z) (eff : SyscallEffect) : bool :=
  match eff with
  | mkEffectU r [] [] [] [] [] => bv_eqb r (errno_ret code)
  | _ => false
  end.

Ltac srw E := rewrite E; cbv beta iota zeta.
Tactic Notation "hrw" constr(E) "in" hyp(H) :=
  rewrite E in H; cbv beta iota zeta in H.

(** Rewrite an equation wherever it applies and re-reduce everything —
    used when [inv_ok] has already renamed the interesting hypothesis. *)
Tactic Notation "hall" constr(E) :=
  try rewrite E in *; cbv beta iota zeta in *.

Lemma error_b_big : forall r,
  addr_is_error_b r = true -> (18446744073709547520 < bv_unsigned r)%Z.
Proof.
  intros r H. unfold addr_is_error_b, two_pow_64 in H.
  apply Z.ltb_lt in H. lia.
Qed.

Ltac bool_true :=
  repeat first
  [ rewrite bv_eqb_refl
  | match goal with
    | H : ?x = ?y |- context [bv_eqb ?x ?y] =>
        rewrite (proj2 (bv_eqb_eq x y) H)
    | H : ?x = ?y |- context [(?x =? ?y)%Z] =>
        rewrite (proj2 (Z.eqb_eq x y) H)
    | H : ?b = true |- context [?b] =>
        lazymatch b with true => fail | _ => rewrite H end
    | |- context [(?a <=? ?b)%Z] =>
        let E := fresh "E" in
        destruct (a <=? b)%Z eqn:E;
        [ clear E | apply Z.leb_gt in E; lia ]
    | |- context [(?a <? ?b)%Z] =>
        let E := fresh "E" in
        destruct (a <? b)%Z eqn:E;
        [ clear E | apply Z.ltb_ge in E; lia ]
    end ].

(** [bind_ok] with the event concatenation as an explicit equation. *)

Lemma bind_ok_eq {A B} :
  forall (c : Sys A) (k : A -> Sys B) i m x m1 evs1 y m2 evs2 evs,
  c i m (Ok x m1 evs1) -> k x i m1 (Ok y m2 evs2) -> evs = evs1 ++ evs2 ->
  bind c k i m (Ok y m2 evs).
Proof. intros; subst; eapply bind_ok; eauto. Qed.

(** [bind_ok] specialised to a first component that emits no events —
    every reader/state accessor in the DSL.  (Plain [bind_ok] cannot be
    [eapply]ed against a CONCRETE event list: [?evs1 ++ ?evs2] does not
    unify with it.) *)

Lemma bind_ok0 {A B} :
  forall (c : Sys A) (k : A -> Sys B) i m x m1 y m2 evs,
  c i m (Ok x m1 []) -> k x i m1 (Ok y m2 evs) ->
  bind c k i m (Ok y m2 evs).
Proof.
  intros. replace evs with ([] ++ evs) by reflexivity. eapply bind_ok; eauto.
Qed.

Lemma check_ret_only_ok_iff : forall eff r m1 evs1 m' evs,
  check_ret_only eff r m1 evs1 = CheckOk m' evs <->
  (eff = mkEffect r [] [] /\ m' = m1 /\ evs = evs1).
Proof.
  intros [ret ws zs us cs copyins] r m1 evs1 m' evs; cbn.
  destruct ws as [|w ws];
    [destruct zs as [|z zs];
      [destruct us as [|u us]; [destruct cs as [|c cs]; [destruct copyins|]|]|]|].
  - destruct (bv_eqb ret r) eqn:E.
    + apply bv_eqb_eq in E; subst.
      split; [intro H; inversion H; auto | intros (H1 & -> & ->)].
      reflexivity.
    + split; [discriminate|]. intros (H1 & _ & _). inversion H1; subst.
      rewrite bv_eqb_refl in E; discriminate.
  - split; [discriminate|]. intros (H1 & _ & _). discriminate H1.
  - split; [discriminate|]. intros (H1 & _ & _). discriminate H1.
  - split; [discriminate|]. intros (H1 & _ & _). discriminate H1.
  - split; [discriminate|]. intros (H1 & _ & _). discriminate H1.
  - split; [discriminate|]. intros (H1 & _ & _). discriminate H1.
Qed.

Lemma check_ret_only_copyins_ok_iff : forall reads eff r m1 evs1 m' evs,
  check_ret_only_copyins reads eff r m1 evs1 = CheckOk m' evs <->
  (eff = with_copyins reads (mkEffect r [] []) /\ m' = m1 /\ evs = evs1).
Proof.
  intros reads [ret ws zs us cs copyins] r m1 evs1 m' evs.
  unfold check_ret_only_copyins.
  change
    ((match check_ret_only (mkEffectU ret ws zs us cs []) r m1 evs1 with
      | CheckOk m'' evs' =>
          if access_ranges_eqb copyins reads
          then CheckOk m'' evs'
          else CheckReject
      | result => result
      end) = CheckOk m' evs <->
     (mkEffectU ret ws zs us cs copyins =
        with_copyins reads (mkEffect r [] []) /\
      m' = m1 /\ evs = evs1)).
  destruct (check_ret_only (mkEffectU ret ws zs us cs []) r m1 evs1)
    as [m'' evs'| |] eqn:Hcore.
  - destruct (access_ranges_eqb copyins reads) eqn:Hr.
    + apply access_ranges_eqb_eq in Hr; subst copyins.
      apply check_ret_only_ok_iff in Hcore.
      destruct Hcore as (Heff & -> & ->). inversion Heff; subst.
      split; [intro H; inversion H; auto|intros (H & -> & ->); inversion H; auto].
    + split; [discriminate|]. intros (H & _ & _). inversion H; subst.
      rewrite (proj2 (access_ranges_eqb_eq reads reads) eq_refl) in Hr.
      discriminate.
  - split; [discriminate|]. intros (H & _ & _). inversion H; subst.
    pose proof (proj2 (check_ret_only_ok_iff (mkEffect r [] []) r m1 evs1 m1 evs1)
      (conj eq_refl (conj eq_refl eq_refl))) as Hok.
    rewrite Hcore in Hok. discriminate.
  - split; [discriminate|]. intros (H & _ & _). inversion H; subst.
    cbn in Hcore. rewrite bv_eqb_refl in Hcore. discriminate.
Qed.

Lemma check_ret_only_no_unmodeled : forall eff r m1 evs1,
  check_ret_only eff r m1 evs1 <> CheckUnmodeled.
Proof.
  intros [ret ws zs us cs copyins] r m1 evs1; cbn.
  destruct ws;
    [destruct zs; [destruct us; [destruct cs; [destruct copyins; [destruct (bv_eqb ret r)|]|]|]|]|];
    discriminate.
Qed.

Lemma check_ret_only_copyins_no_unmodeled : forall reads eff r m1 evs1,
  check_ret_only_copyins reads eff r m1 evs1 <> CheckUnmodeled.
Proof.
  intros. unfold check_ret_only_copyins.
  destruct (check_ret_only (clear_copyins eff) r m1 evs1) eqn:Hcore.
  - destruct (access_ranges_eqb (eff_copyins eff) reads); discriminate.
  - discriminate.
  - exfalso. now apply check_ret_only_no_unmodeled in Hcore.
Qed.

Lemma check_ret_only_copyins_refl : forall reads r m evs,
  check_ret_only_copyins reads (with_copyins reads (mkEffect r [] []))
    r m evs = CheckOk m evs.
Proof.
  intros. unfold check_ret_only_copyins, clear_copyins.
  change ((match check_ret_only (mkEffect r [] []) r m evs with
           | CheckOk m'' evs' =>
               if access_ranges_eqb reads reads
               then CheckOk m'' evs'
               else CheckReject
           | result => result
           end) = CheckOk m evs).
  rewrite (proj2 (check_ret_only_ok_iff _ _ _ _ _ _)
    (conj eq_refl (conj eq_refl eq_refl))).
  rewrite (proj2 (access_ranges_eqb_eq reads reads) eq_refl).
  reflexivity.
Qed.

(** Decompose monadic hypotheses (after the combinators are unfolded). *)
Ltac inv_ok :=
  repeat first
  [ progress subst
  | progress cbv beta zeta in *
  | match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : Ok _ _ _ = Ok _ _ _ |- _ => inversion H; clear H
    | H : Ok _ _ _ = Unmodeled |- _ => discriminate H
    | H : Unmodeled = Ok _ _ _ |- _ => discriminate H
    | H : Some _ = Some _ |- _ => inversion H; clear H
    | H : Some _ = None |- _ => discriminate H
    | H : None = Some _ |- _ => discriminate H
    | H : CheckOk _ _ = CheckOk _ _ |- _ => inversion H; clear H
    | H : False |- _ => contradiction
    | H : _ \/ _ |- _ => destruct H
    end ].

Ltac sys_unfold :=
  (* sugar first, primitive combinators last, so everything bottoms out *)
  unfold record_copyins, with_copyins,
    err_ret, ret_only, errno_from, lowest_fd,
    set_fds, set_pipes, set_vmmaps, add_vm_lazy, forget_vm_range,
    set_stdin, set_urandom, set_fs, set_halted, set_tid,
    set_rlimit_core, set_utsname, set_statpin, set_setsid_succeeded, set_clock, set_creds,
    set_sigmask, set_sigaltstack_installed,
    set_sigmask_deliver, set_sigabrt_pending, set_killed,
    get_model, get_fds, get_vmmaps, modify, input, sysno, arg,
    bind, pure, choose, alt, unmodeled, emit in *.

(* Bridges for the channel short-write acceptors: the claimed return
   decodes to the delivered prefix's length. *)

Lemma len_word_unsigned : forall {A} (l : list A),
  (Z.of_nat (length l) < two_pow_64)%Z ->
  bv_unsigned (len_word l) = Z.of_nat (length l).
Proof.
  intros A l Hl. unfold len_word.
  rewrite Z_to_bv_small; [reflexivity|].
  unfold bv_modulus. change (Z.of_N 64) with 64%Z.
  unfold two_pow_64 in Hl. lia.
Qed.

Lemma firstn_length_le_Z : forall {A} (l : list A) r,
  (0 <= r)%Z -> (r <= Z.of_nat (length l))%Z ->
  Z.of_nat (length (firstn (Z.to_nat r) l)) = r.
Proof.
  intros A l r H0 Hle. rewrite firstn_length_le; lia.
Qed.

(** The delivered prefix's [len_word] is the return value that selected
    it — the step every short-write site would otherwise re-derive. *)

Lemma len_word_firstn_ret : forall (ret : word) {A} (l : list A),
  (0 <= bv_unsigned ret <= Z.of_nat (length l))%Z ->
  len_word (firstn (Z.to_nat (bv_unsigned ret)) l) = ret.
Proof.
  intros ret A l H. unfold len_word.
  rewrite (firstn_length_le_Z l (bv_unsigned ret)) by lia.
  apply Z_to_bv_bv_unsigned.
Qed.

(* ------------------------------------------------------------------ read *)

Lemma neq_einval_of_not_error : forall r,
  addr_is_error_b r = false -> bv_eqb (errno_ret EINVAL) r = false.
Proof.
  intros r H. destruct (bv_eqb (errno_ret EINVAL) r) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. subst r.
  rewrite (errno_ret_error_b EINVAL) in H by (unfold EINVAL; lia). discriminate.
Qed.

Lemma eff_is_errno_true : forall code eff,
  eff_is_errno code eff = true -> eff = mkEffect (errno_ret code) [] [].
Proof.
  intros code [ret ws zs us cs copyins] H. unfold eff_is_errno in H.
  destruct ws; [destruct zs; [destruct us; [destruct cs; [destruct copyins|]|]|]|]; try discriminate.
  apply bv_eqb_eq in H. subst. reflexivity.
Qed.

