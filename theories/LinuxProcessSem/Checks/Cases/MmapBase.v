(** * LinuxProcessSem.Checks.Cases.MmapBase — the mmap-base band is the set of bases Linux gives

    Mirrors [State.mmap_base_min], [State.mmap_base_max] and
    [Run.valid_mmap_base].  Those notes derive the band from mm/util.c's
    [mmap_base] (Linux v6.18.46, commit 1f99e9ab748f).  This file states
    that computation in Rocq and proves the band EQUAL to the set of
    bases it gives under the configuration SCOPE.md names:

    - the top-down layout (no [ADDR_COMPAT_LAYOUT] personality,
      [vm.legacy_va_layout] = 0, and the 8 MiB stack limit);
    - [vm.mmap_rnd_bits] at most 24, or a [stack_guard_gap] of at most
      [floor_guard_max] = 0x4aba6a2ab000 bytes (about 74.7 TiB).

    So a launch inside that configuration has its base in the band, and
    every base in the band is one such a launch can have.  The file also
    shows that each named assumption is needed: without it, Linux gives a
    base under the floor.

    Why the floor is not simply lowered to the smallest base Linux can
    give at all: the ASan plan checker reads it.  [Common.AsanInit]
    starts its placement split at [AsanPlanCore.MBASE_MIN], which is
    [State.mmap_base_min], and [AsanPlacement.kHighMemBeg_below_mmap_base_min]
    needs the floor above the ASan high shadow.  A lower floor would make
    those proofs false, not only longer.

    [Checks/Examples.v] keeps what is not per-syscall and re-exports
    this module; the helper lemmas are [Local], so the re-export adds
    only the definitions and the results.  Reason 3 of that file
    applies: the base is a model constant that no trace reveals. *)

From Stdlib Require Import ZArith Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
Local Open Scope Z_scope.

(** ** The kernel's computation, in [Z]

    The kernel computes the gap in [unsigned long], and so does
    [unclamped_gap]: [pad] wraps at mm/util.c:450, and the test at
    :452-454 keeps the gap at the rlimit when [gap + pad] wraps.  The
    final subtraction is kept in [Z]: a NEGATIVE result is a base that
    wrapped below zero in the kernel; the Sv39 section says why no
    program starts from one. *)

(** [MIN_GAP], mm/util.c:431. *)
Definition min_gap : Z := 128 * 1024 * 1024.

(** [MAX_GAP = STACK_TOP / 6 * 5], mm/util.c:432. *)
Definition max_gap (stack_top : Z) : Z := stack_top / 6 * 5.

(** [STACK_RND_MASK << PAGE_SHIFT] for a 64-bit task:
    arch/riscv/include/asm/elf.h:56-58 gives the mask 0x3ffff. *)
Definition stack_rnd_pad : Z := 0x3ffff * page_size.

(** [rlim_stack->rlim_cur]: SCOPE.md fixes the stack limit at 8 MiB. *)
Definition stack_rlimit : Z := 8 * 1024 * 1024.

(** The clamp of mm/util.c:456-459 ([MIN_GAP < MAX_GAP] holds for every
    stack top below). *)
Definition clamp_gap (stack_top gap : Z) : Z :=
  if gap <? min_gap then min_gap
  else if max_gap stack_top <? gap then max_gap stack_top
  else gap.

(** [pad] of mm/util.c:446-450 in [unsigned long]: [stack_guard_gap]
    (mm/mmap.c:941-954: 256 pages by default, any page count on the
    command line) plus the stack pad under [PF_RANDOMIZE]. *)
Definition guard_pad (guard : Z) (randomize : bool) : Z :=
  (guard + (if randomize then stack_rnd_pad else 0)) mod two_pow_64.

(** [gap] before the clamp, mm/util.c:445 and :452-454. *)
Definition unclamped_gap (guard : Z) (randomize : bool) : Z :=
  if stack_rlimit + guard_pad guard randomize <? two_pow_64
  then stack_rlimit + guard_pad guard randomize
  else stack_rlimit.

(** [mmap_base(rnd, rlim_stack)], mm/util.c:434-463.  [randomize] is
    [PF_RANDOMIZE], which adds the stack pad to the gap and makes
    [arch_pick_mmap_layout] draw [rnd] (mm/util.c:467-470). *)
Definition topdown_base (stack_top guard : Z) (randomize : bool) (rnd : Z) : Z :=
  page_round_up_Z
    (stack_top - clamp_gap stack_top (unclamped_gap guard randomize) - rnd).

(** The inputs one launch can have: any page-multiple guard an
    [unsigned long] holds ([val << PAGE_SHIFT], mm/mmap.c:948-950), and
    [rnd] = [k] pages with [k < 2^bits] ([arch_mmap_rnd],
    mm/util.c:399-411), [k = 0] without [PF_RANDOMIZE]. *)
Definition launch_ok (bits guard : Z) (randomize : bool) (k : Z) : Prop :=
  0 <= guard < two_pow_64 /\ guard mod page_size = 0
  /\ 0 <= k < 2 ^ bits /\ (randomize = false -> k = 0).

(** The configuration SCOPE.md names, over the two knobs that move the
    floor.  [vm.mmap_rnd_bits] lies in [mmap_rnd_bits_min ..
    mmap_rnd_bits_max] (the sysctl's range, mm/mmap.c:1528-1536): 18
    (arch/riscv/Kconfig:260-262) to [MMAP_VA_BITS - PAGE_SHIFT - 3]
    (arch/riscv/mm/init.c:850-853, set at boot, :1164-1167), which is 33
    under Sv48 and Sv57 ([MMAP_VA_BITS] is capped at 48,
    arch/riscv/include/asm/pgtable.h:137-140) and 24 under Sv39.  Its
    boot value [CONFIG_ARCH_MMAP_RND_BITS] lies in 18 .. 24
    (arch/Kconfig:1208-1212, arch/riscv/Kconfig:269-271); only root
    raises it past 24, through /proc/sys/vm/mmap_rnd_bits.

    [floor_guard_max] is the largest guard with which even 33 bits keep
    every base at or above the floor: [STACK_TOP - floor - rlimit -
    stack pad - (2^33 - 1) pages].  It does not depend on the bit count;
    with fewer bits a larger guard would do (about 106.6 TiB at 25). *)
Definition floor_guard_max : Z := 0x4aba6a2ab000.

Definition named_config (bits guard : Z) : Prop :=
  18 <= bits <= 33 /\ (bits <= 24 \/ guard <= floor_guard_max).

(** ** Page rounding and the clamp *)

Local Lemma page_round_up_Z_id : forall x,
  x mod page_size = 0 -> page_round_up_Z x = x.
Proof.
  intros x H. unfold page_round_up_Z, page_size in *.
  Z.div_mod_to_equations. lia.
Qed.

Local Lemma page_round_up_Z_aligned : forall x, page_round_up_Z x mod page_size = 0.
Proof.
  intros x. unfold page_round_up_Z. apply Z_mod_mult.
Qed.

(** Rounding up never passes a page boundary at or above [x]. *)
Local Lemma page_round_up_Z_le : forall x a,
  a mod page_size = 0 -> x <= a -> page_round_up_Z x <= a.
Proof.
  intros x a Ha Hx. unfold page_round_up_Z, page_size in *.
  Z.div_mod_to_equations. lia.
Qed.

(** Rounding up reaches every page boundary less than a page above [x]. *)
Local Lemma page_round_up_Z_ge : forall x a,
  a mod page_size = 0 -> a - page_size < x -> a <= page_round_up_Z x.
Proof.
  intros x a Ha Hx. unfold page_round_up_Z, page_size in *.
  Z.div_mod_to_equations. lia.
Qed.

Local Lemma clamp_gap_id : forall st g,
  min_gap <= g <= max_gap st -> clamp_gap st g = g.
Proof.
  intros st g [H1 H2]. unfold clamp_gap.
  destruct (Z.ltb_spec g min_gap); [lia|].
  destruct (Z.ltb_spec (max_gap st) g); lia.
Qed.

Local Lemma clamp_gap_range : forall st g,
  min_gap <= max_gap st ->
  min_gap <= clamp_gap st g <= max_gap st /\ clamp_gap st g <= Z.max min_gap g.
Proof.
  intros st g H. unfold clamp_gap.
  destruct (Z.ltb_spec g min_gap); [lia|].
  destruct (Z.ltb_spec (max_gap st) g); lia.
Qed.

Local Lemma stack_pad_range : forall randomize : bool,
  0 <= (if randomize then stack_rnd_pad else 0) <= stack_rnd_pad.
Proof. intros []; unfold stack_rnd_pad, page_size; lia. Qed.

(** Without a wrap the gap is the plain sum. *)
Local Lemma unclamped_gap_in_domain : forall (guard : Z) (randomize : bool),
  0 <= guard ->
  stack_rlimit + guard + (if randomize then stack_rnd_pad else 0) < two_pow_64 ->
  unclamped_gap guard randomize
  = stack_rlimit + guard + (if randomize then stack_rnd_pad else 0).
Proof.
  intros guard randomize H0 H1. unfold unclamped_gap, guard_pad.
  pose proof (stack_pad_range randomize) as Hp.
  remember (if randomize then stack_rnd_pad else 0) as p eqn:Hpe.
  rewrite Z.mod_small by (clear - H0 H1 Hp; unfold stack_rlimit in H1; lia).
  destruct (Z.ltb_spec (stack_rlimit + (guard + p)) two_pow_64); [ring|].
  exfalso. clear - H1 H. lia.
Qed.

Local Lemma topdown_base_randomized : forall st guard rnd,
  0 <= guard -> stack_rlimit + guard + stack_rnd_pad < two_pow_64 ->
  topdown_base st guard true rnd
  = page_round_up_Z (st - clamp_gap st (stack_rlimit + guard + stack_rnd_pad) - rnd).
Proof.
  intros st guard rnd H0 H1. unfold topdown_base.
  rewrite (unclamped_gap_in_domain guard true H0 H1). reflexivity.
Qed.

Local Lemma topdown_base_fixed : forall st guard rnd,
  0 <= guard -> stack_rlimit + guard + 0 < two_pow_64 ->
  topdown_base st guard false rnd
  = page_round_up_Z (st - clamp_gap st (stack_rlimit + guard + 0) - rnd).
Proof.
  intros st guard rnd H0 H1. unfold topdown_base.
  rewrite (unclamped_gap_in_domain guard false H0 H1). reflexivity.
Qed.

Local Lemma two_pow_64_val : two_pow_64 = 18446744073709551616.
Proof. reflexivity. Qed.

Local Lemma sv48_domain : sp_window_hi + stack_rnd_pad < two_pow_64.
Proof. vm_compute. reflexivity. Qed.

Local Lemma sv39_domain : sv39_task_size + stack_rnd_pad < two_pow_64.
Proof. vm_compute. reflexivity. Qed.

Local Lemma max_gap_sv48 : max_gap sp_window_hi = 0x6aaaaaaaaaa9.
Proof. vm_compute. reflexivity. Qed.

Local Lemma max_gap_sv39 : max_gap sv39_task_size = 0x3555555552.
Proof. vm_compute. reflexivity. Qed.

(** Every page-aligned [b] from the base of the largest page-multiple
    gap [gmax] with the largest draw of [kmax] pages, up to
    [STACK_TOP - MIN_GAP], is a base some launch has: inside the
    top-down range of [gmax] the guard sets the gap exactly and nothing
    is drawn; below it the gap is [gmax] and the draw makes up the
    rest. *)
Local Lemma every_aligned_base_is_reached : forall st gmax kmax b,
  0 <= kmax -> st mod page_size = 0 -> gmax mod page_size = 0 ->
  stack_rlimit + stack_rnd_pad <= gmax <= max_gap st -> min_gap <= gmax -> gmax <= st ->
  st + stack_rnd_pad < two_pow_64 ->
  b mod page_size = 0 -> 0 <= b -> st - gmax - kmax * page_size <= b <= st - min_gap ->
  exists guard randomize k,
    0 <= guard /\ guard mod page_size = 0
    /\ stack_rlimit + guard + stack_rnd_pad < two_pow_64
    /\ 0 <= k <= kmax /\ (randomize = false -> k = 0)
    /\ b = topdown_base st guard randomize (k * page_size).
Proof.
  intros st gmax kmax b Hkmax Hst Hg Hg1 Hg2 Hg3 Hdom Hb Hb0 [Hlo Hhi].
  assert (exists s, st = page_size * s) as [s Hs]
    by (exists (st / page_size); unfold page_size in *; Z.div_mod_to_equations; lia).
  assert (exists g, gmax = page_size * g) as [g Hgs]
    by (exists (gmax / page_size); unfold page_size in *; Z.div_mod_to_equations; lia).
  assert (exists m, b = page_size * m) as [m Hm]
    by (exists (b / page_size); unfold page_size in *; Z.div_mod_to_equations; lia).
  destruct (Z_lt_le_dec b (st - gmax)) as [Hb'|Hb'].
  - exists (gmax - stack_rlimit - stack_rnd_pad), true, (s - g - m).
    rewrite topdown_base_randomized
      by (clear - Hg1 Hg3 Hdom; unfold stack_rlimit, stack_rnd_pad, page_size in *; lia).
    replace (stack_rlimit + (gmax - stack_rlimit - stack_rnd_pad) + stack_rnd_pad)
      with gmax by ring.
    rewrite (clamp_gap_id st gmax) by (clear - Hg1 Hg2; lia).
    rewrite page_round_up_Z_id
      by (unfold page_size in *; Z.div_mod_to_equations; lia).
    unfold stack_rlimit, stack_rnd_pad, page_size in *.
    repeat split.
    all: try (intros Hf; discriminate Hf).
    all: try (Z.div_mod_to_equations; lia).
  - exists (st - b - stack_rlimit), false, 0.
    rewrite topdown_base_fixed
      by (clear - Hhi Hb0 Hdom; unfold stack_rlimit, stack_rnd_pad, min_gap, page_size in *; lia).
    replace (stack_rlimit + (st - b - stack_rlimit) + 0) with (st - b) by ring.
    rewrite (clamp_gap_id st (st - b)) by (clear - Hhi Hb' Hg1; lia).
    rewrite page_round_up_Z_id
      by (unfold page_size in *; Z.div_mod_to_equations; lia).
    unfold stack_rlimit, stack_rnd_pad, min_gap, page_size in *.
    repeat split.
    all: try (Z.div_mod_to_equations; lia).
Qed.

(** ** Sv48 (and Sv57, which has the same stack top and the same bit range)

    The band is EXACTLY the set of bases the named configuration gives.
    Left to right needs only [bits = 24]: the floor is the base with the
    largest gap and the largest 24-bit draw.  Right to left is the
    derivation in [State.mmap_base_min]'s note, for every input. *)

Definition sv48_linux_base (b : Z) : Prop :=
  exists bits guard randomize k,
    named_config bits guard /\ launch_ok bits guard randomize k
    /\ b = topdown_base sp_window_hi guard randomize (k * page_size).

Theorem sv48_band_is_linux_set : forall w : word,
  valid_mmap_base w <-> sv48_linux_base (bv_unsigned w).
Proof.
  intros w. unfold valid_mmap_base, sv48_linux_base, named_config, launch_ok.
  split.
  - intros (Hlo & Hhi & Hal).
    unfold mmap_base_min, mmap_base_max, sp_window_hi in Hlo, Hhi.
    destruct (every_aligned_base_is_reached sp_window_hi 0x6aaaaaaaa000 16777215
                (bv_unsigned w) ltac:(lia) eq_refl eq_refl
                ltac:(rewrite max_gap_sv48; unfold stack_rlimit, stack_rnd_pad, page_size; lia)
                ltac:(unfold min_gap; lia) ltac:(unfold sp_window_hi; lia) sv48_domain Hal
                ltac:(lia) ltac:(unfold sp_window_hi, min_gap, page_size; lia))
      as (guard & randomize & k & H1 & H2 & H3 & H4 & H5 & H6).
    assert (Hp24 : 2 ^ 24 = 16777216) by reflexivity.
    unfold stack_rlimit, stack_rnd_pad, page_size in H3.
    exists 24, guard, randomize, k. rewrite Hp24.
    split; [split; [lia | left; lia]|].
    split; [repeat split; try assumption; lia | exact H6].
  - intros (bits & guard & randomize & k & (Hb1 & Hcfg) & ((Hg0 & Hglt) & Hgal & Hk & Hk0) & ->).
    unfold topdown_base.
    pose proof (clamp_gap_range sp_window_hi (unclamped_gap guard randomize))
      as [[Hc1 Hc2] Hc3]; [rewrite max_gap_sv48; unfold min_gap; lia|].
    rewrite max_gap_sv48 in Hc2.
    remember (clamp_gap sp_window_hi (unclamped_gap guard randomize)) as c eqn:Hce.
    split; [|split; [|apply page_round_up_Z_aligned]].
    + (* the floor *)
      apply page_round_up_Z_ge; [reflexivity|].
      unfold mmap_base_min, sp_window_hi, page_size.
      destruct Hcfg as [Hbits|Hguard].
      * assert (Hpow : 2 ^ bits <= 16777216)
          by (change 16777216 with (2 ^ 24); apply Z.pow_le_mono_r; lia).
        clear - Hc2 Hk Hpow. lia.
      * assert (Hpow : 2 ^ bits <= 8589934592)
          by (change 8589934592 with (2 ^ 33); apply Z.pow_le_mono_r; lia).
        pose proof (stack_pad_range randomize) as Hp.
        rewrite unclamped_gap_in_domain in Hc3
          by (clear - Hg0 Hguard Hp; try rewrite two_pow_64_val;
              unfold floor_guard_max, stack_rlimit, stack_rnd_pad, page_size in *; lia).
        remember (if randomize then stack_rnd_pad else 0) as p eqn:Hpe.
        clear - Hc3 Hk Hpow Hguard Hp.
        unfold floor_guard_max, stack_rlimit, stack_rnd_pad, min_gap, page_size in *. lia.
    + (* the cap *)
      apply page_round_up_Z_le; [reflexivity|].
      unfold mmap_base_max, sp_window_hi, min_gap, page_size in *. clear - Hc1 Hk. lia.
Qed.

(** Each assumption is needed.  With 25 bits and a guard that drives the
    gap to its largest page multiple, the draw of [2^24] pages gives
    0x154555556000, one page under the floor. *)
Example rnd_bits_25_and_a_huge_guard_go_below_the_floor :
  launch_ok 25 (0x6aaaaaaaa000 - stack_rlimit - stack_rnd_pad) true (2 ^ 24)
  /\ topdown_base sp_window_hi (0x6aaaaaaaa000 - stack_rlimit - stack_rnd_pad) true
       (2 ^ 24 * page_size) = 0x154555556000
  /\ 0x154555556000 < mmap_base_min.
Proof.
  unfold launch_ok. repeat split; try (intros Hf; discriminate Hf);
    vm_compute; try reflexivity; discriminate.
Qed.

(** The legacy layout puts the base at [TASK_UNMAPPED_BASE] plus the draw
    (mm/util.c:472-474), where [TASK_UNMAPPED_BASE] is
    [PAGE_ALIGN(2^MMAP_MIN_VA_BITS / 3)] with [MMAP_MIN_VA_BITS] = 39 for
    a 64-bit task (arch/riscv/include/asm/processor.h:52,
    arch/riscv/include/asm/pgtable.h:138-140).  Without a draw that is
    far under the floor. *)
Definition task_unmapped_base : Z := page_round_up_Z (2 ^ 39 / 3).

Example legacy_base_is_below_the_floor :
  task_unmapped_base = 0x2aaaaab000 /\ task_unmapped_base < mmap_base_min.
Proof. split; vm_compute; reflexivity. Qed.

(** And the clause that covers the hardened setting: root raises
    [vm.mmap_rnd_bits] to 33 and leaves the guard at its default 256
    pages.  The lowest base that gives is 0x5fffbf702000, well inside the
    band, so that setting is in the model. *)
Example rnd_bits_33_default_guard_is_in_the_band :
  named_config 33 (256 * page_size)
  /\ topdown_base sp_window_hi (256 * page_size) true ((2 ^ 33 - 1) * page_size)
     = 0x5fffbf702000
  /\ mmap_base_min <= 0x5fffbf702000.
Proof.
  split; [split; [lia | right; vm_compute; discriminate]|].
  split; vm_compute; [reflexivity | discriminate].
Qed.

(** [floor_guard_max] is exact: at 33 bits with the largest draw, that
    guard gives the floor itself and one page more gives a base one page
    under it. *)
Example floor_guard_max_is_tight :
  topdown_base sp_window_hi floor_guard_max true ((2 ^ 33 - 1) * page_size)
    = mmap_base_min
  /\ launch_ok 33 (floor_guard_max + page_size) true (2 ^ 33 - 1)
  /\ topdown_base sp_window_hi (floor_guard_max + page_size) true
       ((2 ^ 33 - 1) * page_size) = mmap_base_min - page_size.
Proof.
  unfold launch_ok. repeat split; try (intros Hf; discriminate Hf);
    vm_compute; try reflexivity; discriminate.
Qed.

(** ** Sv39

    [STACK_TOP] is 2^38 and [mmap_rnd_bits_max] is 24, so the
    subtraction can go below zero and wrap.  Such a base gives no
    program: the vDSO's [get_unmapped_area] (arch/riscv/kernel/vdso.c:124-127)
    takes the top-down search with [high_limit] = the wrapped base
    (mm/mmap.c:766), which finds the free range above the stack
    (mm/vma.c:2942-2982) and answers an address above [TASK_SIZE];
    [__get_unmapped_area] turns that into [-ENOMEM] (mm/mmap.c:857-858),
    [load_elf_binary] fails past the point of no return
    (fs/binfmt_elf.c:1290-1293) and [bprm_execve] kills the task
    (fs/exec.c:1774-1775).  So the Sv39 band is every page-aligned base
    from 0 to the cap, and it is exactly the set of non-wrapped bases.
    Base 0 is in that set and also starts no program: the search's top
    is then [0 - 1] = [ULONG_MAX] (mm/vma.h:502), so the vDSO search
    fails as for a wrapped base.  The band keeps it, a precision cost
    only, since no spec arm reads the base. *)

Definition sv39_linux_base (b : Z) : Prop :=
  exists guard randomize k,
    launch_ok 24 guard randomize k
    /\ b = topdown_base sv39_task_size guard randomize (k * page_size).

Theorem sv39_band_is_linux_set : forall w : word,
  valid_mmap_base_va Sv39 w <-> sv39_linux_base (bv_unsigned w).
Proof.
  intros w.
  cbv [valid_mmap_base_va va_mmap_base_min va_mmap_base_max va_stack_top].
  unfold sv39_linux_base, launch_ok.
  pose proof (bv_unsigned_in_range 64 w) as [Hw0 _].
  split.
  - intros (_ & Hhi & Hal).
    destruct (every_aligned_base_is_reached sv39_task_size 0x3555555000 16777215
                (bv_unsigned w) ltac:(lia) eq_refl eq_refl
                ltac:(rewrite max_gap_sv39; unfold stack_rlimit, stack_rnd_pad, page_size; lia)
                ltac:(unfold min_gap; lia) ltac:(unfold sv39_task_size; lia) sv39_domain Hal Hw0
                ltac:(unfold sv39_task_size, min_gap, page_size in *; lia))
      as (guard & randomize & k & H1 & H2 & H3 & H4 & H5 & H6).
    assert (Hp24 : 2 ^ 24 = 16777216) by reflexivity.
    unfold stack_rlimit, stack_rnd_pad, page_size in H3.
    exists guard, randomize, k. rewrite Hp24.
    split; [repeat split; try assumption; lia | exact H6].
  - intros (guard & randomize & k & ((Hg0 & Hglt) & Hgal & Hk & Hk0) & Heq).
    pose proof (clamp_gap_range sv39_task_size (unclamped_gap guard randomize))
      as [[Hc1 Hc2] _]; [rewrite max_gap_sv39; unfold min_gap; lia|].
    rewrite max_gap_sv39 in Hc2.
    split; [lia|split; [|rewrite Heq; apply page_round_up_Z_aligned]].
    rewrite Heq. unfold topdown_base.
    remember (clamp_gap sv39_task_size (unclamped_gap guard randomize)) as c eqn:Hce.
    apply page_round_up_Z_le; [reflexivity|].
    unfold sv39_task_size, min_gap, page_size in *. clear - Hc1 Hk. lia.
Qed.
