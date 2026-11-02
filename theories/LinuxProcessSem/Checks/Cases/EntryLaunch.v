(** * LinuxProcessSem.Checks.Cases.EntryLaunch — the admitted start states are Linux's

    Mirrors [Run.entry_launch_ok_va], the fifth conjunct of
    [Run.valid_entry_va], the way [Checks.Cases.MmapBase] mirrors
    [Run.valid_mmap_base]: that file states mm/util.c's [mmap_base] in
    Rocq and proves the band EQUAL to the set of bases Linux gives;
    this one states the whole of the kernel's entry arithmetic and
    proves the conjunct EQUAL to the set of start states a Linux
    v6.18.46 (commit 1f99e9ab748f) launch gives.

    THE FIXTURE, acceptance item A1 of the start-state specification: argv
    ["a"], no envp, exec file name "a", uid = gid = 1000, AT_HWCAP
    without V, CONFIG_RSEQ on, a guard gap of 256 pages,
    [vm.mmap_rnd_bits] 18, no vector unit, no cache leaf reported and
    the first vDSO image.  With those the auxv is 29 entries, [items]
    is 4, C = 512 and L = 4.  Everything below is under Sv48 except
    [entry_launch_ok_va_is_linux], which is stated for every
    [State.VaSize], every entry and every input.

    WHICH RESULT IS WHICH ACCEPTANCE BULLET.  A1 lists eleven things to
    pin; each has one name here.

    - admitted without randomization, [ed_top] = 0x800000000000,
      sp = 0x7ffffffffdf0, base = 0x7ffff8000000:
      [a1_no_aslr_admitted].
    - admitted with randomization, [ed_top] = 0x7fffc0000000,
      sp = 0x7fffbfffedf0, base 0x7fffbf701000 (no mmap draw) or
      0x7fff7f702000 (the draw at its largest, 18 bits):
      [a1_aslr_admitted_base_hi] and [a1_aslr_admitted_base_lo].
    - refused for every [ed_top] and every value of the launch facts,
      sp = 0x7fffe0000000 with base = 0x7ffff8000000 (kind 1):
      [a1_kind1_pair_refused].
    - refused for every [ed_top] and every value of the launch facts,
      sp = 0x7fff80000000 with base = 0x154555557000 (kind 2):
      [a1_kind2_sp_refused].
    - refused for every [ed_top] without randomization,
      sp = 0x7fffffffdde0 with base = 0x7ffff8000000, sixteen bytes
      below the bottom 0x7fffffffddf0 of the raced range:
      [a1_sp_below_raced_range_refused].
    - refused for every sp and every [ed_top] (kind 5):
      [a1_kind5_base_with_aslr_refused] (base = 0x7ffff8000000 with
      randomization) and [a1_kind5_base_without_aslr_refused]
      (base = 0x7fffbf701000 without it).
    - refused, the two edges of rule 1: [a1_top_below_range_refused]
      ([ed_top] = 0x7fffbffff000 with randomization) and
      [a1_top_two_pages_down_refused] ([ed_top] = 0x7fffffffe000
      without it).
    - [Run.valid_launch] false for an argv Linux refuses with E2BIG and
      for the empty exec name: [a1_e2big_argv_refused] and
      [a1_empty_execfn_refused].
    - the block of the first admitted entry, byte for byte against a
      hand computation from the spec's "The block":
      [a1_block_length], [a1_block_addresses], [a1_block_head_words],
      [a1_block_auxv_is_linuxs] and [a1_block_is_linuxs_bytes].
    - [entry_launch_ok_va_is_linux]: the conjunct holds EXACTLY when
      some draws give that stack top, stack pointer and mmap base
      through the transcription [linux_launch_state] of
      [randomize_stack_top] and [setup_arg_pages] (mm/util.c,
      fs/exec.c), [create_elf_tables] (fs/binfmt_elf.c) and [mmap_base]
      with [arch_mmap_rnd] (mm/util.c).
    - every valid input still has an entry, so the quantifier of every
      statement is not empty: [a1_witness_entry_is_valid], which fires
      [Run.launch_entry_va_valid] on the fixture.

    [Checks/Examples.v] keeps what is not per-syscall and re-exports
    this module; the helper lemmas are [Local], so the re-export adds
    only the definitions and the results. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType.
Import ListNotations.
Local Open Scope Z_scope.

(* ========================================================================= *)
(** ** The kernel's three steps, in Rocq                                     *)
(* ========================================================================= *)

(** [randomize_stack_top(STACK_TOP)] (mm/util.c) followed by
    [setup_arg_pages]'s [arch_align_stack] and [PAGE_ALIGN]
    (fs/exec.c, arch/riscv/kernel/process.c, Linux v6.18.46, commit
    1f99e9ab748f).

    [k] is the page draw, 0 to 0x3ffff under PF_RANDOMIZE and 0
    otherwise ([STACK_RND_MASK], arch/riscv/include/asm/elf.h); [r'] is
    the byte [arch_align_stack] subtracts, 0 to 4095
    ([get_random_u32_below(PAGE_SIZE)]).  From a page-aligned [T],
    [(T - r') & ~0xf] is [T - 4096] for [r'] above 4080 and above
    [T - 4096] otherwise, so [PAGE_ALIGN] gives [T] for the smaller
    draws.  That is why the admitted set is one page wider than the
    page draw, and why only the two ends of [r'] are computed below:
    the value set is {T, T - 4096} whatever the boundary is. *)
Definition linux_stack_top (v : VaSize) (k r' : Z) : Z :=
  page_round_up_Z (align_down16 (va_stack_top v - page_size * k - r')).

(** [create_elf_tables] (fs/binfmt_elf.c), from [bprm->p = top - 8 - L]
    down:

      [p = arch_align_stack(p);]            minus [r] in [0, 4095], then & ~0xf
      [u_rand_bytes = STACK_ALLOC(p, 16);]  p -= 16
      [sp = STACK_ADD(p, ei_index);]        p - 16 * n_aux
      [bprm->p = STACK_ROUND(sp, items);]   (sp - 8 * items) & ~15

    [p] after [arch_align_stack] is 16-aligned and [16 * n_aux] is a
    multiple of 16, so the last mask removes exactly [8 * (items mod 2)]
    bytes.  All of that is [StackLayout.block_head_size]. *)
Definition linux_entry_sp (top : Z) (inp : ProcInput) (r : Z) : Z :=
  align_down16 (top - 8
                - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                                (in_execfn inp))
                - r)
  - Z.of_nat (block_head_size (kb_rseq (in_kernel inp))
                              (in_argv inp) (in_envp inp)).

(** [arch_pick_mmap_layout] and [mmap_base] (mm/util.c).
    [Run.mmap_base_of] is the transcription — [Checks.Cases.MmapBase]
    proves that one equal to the kernel's computation — and [q] is
    [arch_mmap_rnd]'s
    [get_random_long() & ((1UL << mmap_rnd_bits) - 1)], which the shift
    by PAGE_SHIFT turns into [page_size * q], and which is 0 without
    PF_RANDOMIZE. *)
Definition linux_mmap_base (v : VaSize) (kb : KernelBuild) (q : Z) : Z :=
  mmap_base_of v kb (page_size * q).

(** THE START STATE OF ONE LAUNCH: the four draws, each with the range
    the kernel's own code gives it.  They are four and not three
    because [arch_align_stack] is called TWICE and reads a fresh
    random each time — once in [setup_arg_pages] ([r']) and once in
    [create_elf_tables] ([r]) — and the mmap draw [q] is a third
    source ([arch_mmap_rnd]).

    Without PF_RANDOMIZE the stack page draw and the mmap draw are 0,
    while [r] and [r'] are NOT: [load_elf_binary] reads
    [randomize_va_space] once for PF_RANDOMIZE, and [arch_align_stack]
    reads the global again at each call, so a root write to the sysctl
    during the [execve] gives the pad with no draw. *)
Definition linux_launch_state (v : VaSize) (inp : ProcInput)
    (k r' r q : Z) (top sp mbase : Z) : Prop :=
  let kb := in_kernel inp in
  (0 <= k <= 0x3ffff) /\ (kb_aslr kb = false -> k = 0)
  /\ (0 <= r' <= 4095)
  /\ (0 <= r <= 4095)
  /\ (0 <= q) /\ (kb_aslr kb = true -> q < 2 ^ mmap_rnd_bits v kb)
  /\ (kb_aslr kb = false -> q = 0)
  /\ top = linux_stack_top v k r'
  /\ sp = linux_entry_sp top inp r
  /\ mbase = linux_mmap_base v kb q.

(* ========================================================================= *)
(** ** Arithmetic the two directions share                                   *)
(* ========================================================================= *)

Local Lemma page_round_up_Z_id : forall x,
  x mod page_size = 0 -> page_round_up_Z x = x.
Proof.
  intros x H. unfold page_round_up_Z, page_size in *.
  Z.div_mod_to_equations. lia.
Qed.

Local Lemma page_round_up_Z_aligned : forall x,
  page_round_up_Z x mod page_size = 0.
Proof. intros x. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Local Lemma page_round_up_Z_le : forall x a,
  a mod page_size = 0 -> x <= a -> page_round_up_Z x <= a.
Proof.
  intros x a Ha Hx. unfold page_round_up_Z, page_size in *.
  Z.div_mod_to_equations. lia.
Qed.

Local Lemma page_round_up_Z_ge : forall x a,
  a mod page_size = 0 -> a - page_size < x -> a <= page_round_up_Z x.
Proof.
  intros x a Ha Hx. unfold page_round_up_Z, page_size in *.
  Z.div_mod_to_equations. lia.
Qed.

Local Lemma align_down16_mono : forall x y, x <= y -> align_down16 x <= align_down16 y.
Proof.
  intros x y H. unfold align_down16.
  pose proof (Z.mod_pos_bound x 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
  pose proof (Z.div_mod x 16 ltac:(lia)).
  pose proof (Z.div_mod y 16 ltac:(lia)).
  assert (x / 16 <= y / 16) by (apply Z.div_le_mono; lia).
  lia.
Qed.

Local Lemma align_down16_mod16 : forall x, align_down16 x mod 16 = 0.
Proof.
  intro x. unfold align_down16.
  pose proof (Z.div_mod x 16 ltac:(lia)).
  replace (x - x mod 16) with (16 * (x / 16)) by lia.
  now rewrite Z.mul_comm, Z.mod_mul.
Qed.

Local Lemma align_down16_le : forall x, align_down16 x <= x.
Proof.
  intro x. unfold align_down16. pose proof (Z.mod_pos_bound x 16 ltac:(lia)). lia.
Qed.

Local Lemma align_down16_ge : forall x, x - 15 <= align_down16 x.
Proof.
  intro x. unfold align_down16. pose proof (Z.mod_pos_bound x 16 ltac:(lia)). lia.
Qed.

(** [x & ~0xf] moves by whole pages when [x] does: 4096 is a multiple
    of 16.  This is what makes the bottom of rule 2's interval
    reachable with a pad of 4095 rather than 4096. *)
Local Lemma align_down16_sub_4096 : forall x,
  align_down16 (x - 4096) = align_down16 x - 4096.
Proof.
  intro x. unfold align_down16.
  replace (x - 4096) with (x + (-256) * 16) by ring.
  rewrite Z_mod_plus_full. ring.
Qed.

(** [align_down16] on the window [arch_align_stack] draws from hits
    every multiple of 16 in the closed interval between its two ends,
    and nothing else: the step from [r] to [r + 1] moves the value by 0
    or 16.  This is what makes rule 2's INTERVAL exactly the set of
    stack pointers [create_elf_tables] (fs/binfmt_elf.c) can produce.

    The second branch is the reason the witness is not simply
    [align_down16 x - s]: when [x] is not 15 mod 16 the two ends are
    4096 apart, so the bottom one needs the pad 4095 and that formula
    would answer 4096, a draw [get_random_u32_below(PAGE_SIZE)] never
    returns. *)
Local Lemma align_down16_surj : forall x s,
  align_down16 (x - 4095) <= s <= align_down16 x -> s mod 16 = 0 ->
  exists r, 0 <= r <= 4095 /\ align_down16 (x - r) = s.
Proof.
  intros x s [Hlo Hhi] Hmod.
  destruct (Z_le_gt_dec (align_down16 x - s) 4095) as [Hd|Hd].
  - exists (align_down16 x - s). split; [lia|].
    unfold align_down16 at 2. unfold align_down16 in Hd, Hhi.
    replace (x - (x - x mod 16 - s)) with (s + x mod 16) by ring.
    unfold align_down16.
    rewrite <- Z.add_mod_idemp_l by lia. rewrite Hmod, Z.add_0_l.
    rewrite Z.mod_mod by lia. ring.
  - exists 4095. split; [lia|].
    pose proof (align_down16_mono (x - 4096) (x - 4095) ltac:(lia)) as Hmo.
    rewrite align_down16_sub_4096 in Hmo. lia.
Qed.

(** C is a multiple of 16, so a stack pointer the kernel produces is
    16-aligned exactly when [align_down16]'s answer is: [8 * items] and
    [8 * (items mod 2)] together make [16 * (items / 2 + items mod 2)],
    which is [STACK_ROUND]'s whole effect
    ([StackLayout.block_head_size]). *)
Local Lemma block_head_size_mult16_nat : forall rseq argv envp,
  exists c, block_head_size rseq argv envp = (16 * c)%nat.
Proof.
  intros rseq argv envp. unfold block_head_size, auxv_size, auxv_count.
  pose proof (Nat.div_mod_eq (block_items argv envp) 2) as Hd.
  pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)) as Hm.
  destruct rseq;
    [ exists (block_items argv envp / 2 + block_items argv envp mod 2 + 30)%nat
    | exists (block_items argv envp / 2 + block_items argv envp mod 2 + 28)%nat ];
    lia.
Qed.

Local Lemma block_head_size_mult16 : forall rseq argv envp,
  exists c, Z.of_nat (block_head_size rseq argv envp) = 16 * c.
Proof.
  intros rseq argv envp.
  destruct (block_head_size_mult16_nat rseq argv envp) as [c Hc].
  exists (Z.of_nat c). rewrite Hc, Nat2Z.inj_mul. reflexivity.
Qed.

Local Lemma exists_page_mult : forall x, x mod 4096 = 0 -> exists q, x = 4096 * q.
Proof. intros x H. exists (x / 4096). Z.div_mod_to_equations. lia. Qed.

(** A page boundary is a 16-byte boundary: [arch_align_stack]'s mask
    never moves a page-aligned address. *)
Local Lemma mod_4096_mod_16 : forall x, x mod 4096 = 0 -> x mod 16 = 0.
Proof.
  intros x H. destruct (exists_page_mult x H) as [q ->].
  replace (4096 * q) with (16 * (256 * q)) by ring.
  rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

Local Lemma va_stack_top_page : forall v, va_stack_top v mod page_size = 0.
Proof. destruct v; reflexivity. Qed.

(** A page-aligned top stays page-aligned under the page draw. *)
Local Lemma stack_T_page : forall v k,
  (va_stack_top v - page_size * k) mod page_size = 0.
Proof.
  intros v k. pose proof (va_stack_top_page v) as HT.
  unfold page_size in *. rewrite Zminus_mod, HT, Z.mul_comm, Z.mod_mul by lia.
  reflexivity.
Qed.

(** Rule 1's value is one of two: the draw's own page, or one page
    below it.  Only the bounds are needed, never the boundary of [r'],
    because the set {T, T - 4096} is the same either side of it. *)
Local Lemma linux_stack_top_bounds : forall v k r',
  0 <= r' <= 4095 ->
  va_stack_top v - page_size * k - page_size <= linux_stack_top v k r'
  <= va_stack_top v - page_size * k.
Proof.
  intros v k r' Hr. unfold linux_stack_top.
  pose proof (stack_T_page v k) as HTm.
  pose proof (align_down16_le (va_stack_top v - page_size * k - r')) as H1.
  pose proof (align_down16_ge (va_stack_top v - page_size * k - r')) as H2.
  split.
  - apply page_round_up_Z_ge.
    + unfold page_size in *. rewrite Zminus_mod, HTm. reflexivity.
    + unfold page_size in *. lia.
  - apply page_round_up_Z_le; [exact HTm|]. lia.
Qed.

(** No [arch_align_stack] pad in [setup_arg_pages]: the top is the page
    draw's own page. *)
Local Lemma linux_stack_top_zero : forall v k,
  linux_stack_top v k 0 = va_stack_top v - page_size * k.
Proof.
  intros v k. pose proof (stack_T_page v k) as HTm.
  unfold linux_stack_top. rewrite Z.sub_0_r.
  assert (H16 : (va_stack_top v - page_size * k) mod 16 = 0)
    by (apply mod_4096_mod_16; exact HTm).
  unfold align_down16. rewrite H16, Z.sub_0_r.
  apply page_round_up_Z_id. exact HTm.
Qed.

(** The largest pad: [(T - 4095) & ~0xf] is exactly [T - 4096] from a
    page-aligned [T], and [PAGE_ALIGN] leaves it there.  That is the
    whole of why rule 1's range is one page wider than
    [STACK_RND_MASK]. *)
Local Lemma linux_stack_top_lo : forall v k,
  linux_stack_top v k 4095 = va_stack_top v - page_size * k - page_size.
Proof.
  intros v k. pose proof (stack_T_page v k) as HTm.
  destruct (exists_page_mult (va_stack_top v - page_size * k) HTm) as [q Hq].
  unfold linux_stack_top. rewrite Hq.
  assert (Hm : (4096 * q - 4095) mod 16 = 1).
  { replace (4096 * q - 4095) with (1 + (256 * q - 256) * 16) by ring.
    rewrite Z.mod_add by lia. reflexivity. }
  unfold align_down16. rewrite Hm.
  replace (4096 * q - 4095 - 1) with (4096 * (q - 1)) by ring.
  rewrite page_round_up_Z_id
    by (unfold page_size; rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity).
  unfold page_size. lia.
Qed.

(* ========================================================================= *)
(** ** The conjunct is the set of Linux launches                             *)
(* ========================================================================= *)

(** Rule 1 ADMITS every launch: a top the transcription produces
    satisfies [Run.valid_stack_top_va]. *)
Local Lemma linux_stack_top_sound : forall v aslr (top : word) k r',
  0 <= k <= 0x3ffff -> (aslr = false -> k = 0) -> 0 <= r' <= 4095 ->
  bv_unsigned top = linux_stack_top v k r' ->
  valid_stack_top_va v aslr top.
Proof.
  intros v aslr top k r' Hk Hk0 Hr' Heq.
  pose proof (linux_stack_top_bounds v k r' Hr') as [Hb1 Hb2].
  unfold valid_stack_top_va. rewrite Heq.
  split; [unfold linux_stack_top; apply page_round_up_Z_aligned|].
  split; [unfold page_size in *; lia|].
  destruct aslr.
  - unfold stack_rnd_max, page_size in *. lia.
  - pose proof (Hk0 eq_refl) as Hk00. subst k.
    unfold page_size in *. lia.
Qed.

(** Rule 1 MISSES no launch: a top the conjunct admits comes from a
    page draw and an [arch_align_stack] pad.  [m] pages below the
    kernel's STACK_TOP is the draw [m] with no pad when [m] is within
    [STACK_RND_MASK], and the largest draw with the largest pad at the
    one page below it. *)
Local Lemma linux_stack_top_complete : forall v aslr (top : word),
  valid_stack_top_va v aslr top ->
  exists k r', 0 <= k <= 0x3ffff /\ (aslr = false -> k = 0)
               /\ 0 <= r' <= 4095
               /\ bv_unsigned top = linux_stack_top v k r'.
Proof.
  intros v aslr top (Hmod & Hhi & Hlo).
  pose proof (va_stack_top_page v) as HT.
  assert (Hdiv : exists m, bv_unsigned top = va_stack_top v - page_size * m
                           /\ 0 <= m).
  { exists ((va_stack_top v - bv_unsigned top) / page_size).
    assert (Hd : (va_stack_top v - bv_unsigned top) mod page_size = 0)
      by (rewrite Zminus_mod, HT, Hmod; reflexivity).
    unfold page_size in *. Z.div_mod_to_equations. lia. }
  destruct Hdiv as [m [Hmv Hm0]].
  destruct aslr.
  - assert (Hmle : m <= 0x40000)
      by (unfold stack_rnd_max, page_size in *; lia).
    destruct (Z_le_gt_dec m 0x3ffff) as [Hsmall|Hbig].
    + exists m, 0. split; [lia|]. split; [intros Hc; discriminate Hc|].
      split; [lia|]. rewrite linux_stack_top_zero. exact Hmv.
    + assert (Hm : m = 0x40000) by lia. subst m.
      exists 0x3ffff, 4095. split; [lia|].
      split; [intros Hc; discriminate Hc|]. split; [lia|].
      rewrite linux_stack_top_lo. unfold page_size in *. lia.
  - assert (Hmle : m <= 1) by (unfold page_size in *; lia).
    destruct (Z.eq_dec m 0) as [Hz|Hnz].
    + subst m. exists 0, 0. split; [lia|]. split; [intros _; reflexivity|].
      split; [lia|]. rewrite linux_stack_top_zero. exact Hmv.
    + assert (Hm : m = 1) by lia. subst m.
      exists 0, 4095. split; [lia|]. split; [intros _; reflexivity|].
      split; [lia|]. rewrite linux_stack_top_lo. unfold page_size in *. lia.
Qed.

(** Rule 2 ADMITS every launch. *)
Local Lemma linux_entry_sp_sound : forall (top sp : word) inp r,
  0 <= r <= 4095 ->
  bv_unsigned sp = linux_entry_sp (bv_unsigned top) inp r ->
  valid_launch_sp top inp sp.
Proof.
  intros top sp inp r Hr Heq.
  destruct (block_head_size_mult16 (kb_rseq (in_kernel inp))
                                   (in_argv inp) (in_envp inp)) as [c Hc].
  unfold valid_launch_sp, launch_sp_lo, launch_sp_hi, linux_entry_sp in *.
  split.
  - rewrite Heq, Hc, Zminus_mod, align_down16_mod16, Z.mul_comm, Z_mod_mult.
    reflexivity.
  - rewrite Heq. split; apply Z.sub_le_mono_r; apply align_down16_mono; lia.
Qed.

(** Rule 2 MISSES no launch: a 16-aligned stack pointer in the
    interval is [align_down16 (top - 8 - L - r) - C] for a pad [r] that
    [arch_align_stack] can draw. *)
Local Lemma linux_entry_sp_complete : forall (top sp : word) inp,
  valid_launch_sp top inp sp ->
  exists r, 0 <= r <= 4095
            /\ bv_unsigned sp = linux_entry_sp (bv_unsigned top) inp r.
Proof.
  intros top sp inp (Hmod & Hlo & Hhi).
  destruct (block_head_size_mult16 (kb_rseq (in_kernel inp))
                                   (in_argv inp) (in_envp inp)) as [c Hc].
  unfold launch_sp_lo, launch_sp_hi in Hlo, Hhi.
  destruct (align_down16_surj
              (bv_unsigned top - 8
               - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                               (in_execfn inp)))
              (bv_unsigned sp
               + Z.of_nat (block_head_size (kb_rseq (in_kernel inp))
                                           (in_argv inp) (in_envp inp))))
    as [r [Hr Hreq]].
  - lia.
  - rewrite Hc, Zplus_mod, Hmod, Z.mul_comm, Z_mod_mult. reflexivity.
  - exists r. split; [exact Hr|]. unfold linux_entry_sp. lia.
Qed.

(** THE ADMITTED SET IS THE SET OF LINUX LAUNCHES, for every
    address-space size, every entry and every input: the fifth
    conjunct of [Run.valid_entry_va] holds of an entry exactly when
    some stack page draw, two [arch_align_stack] pads and one
    [arch_mmap_rnd] draw give its stack top, its stack pointer and its
    mmap base.  [Checks.Cases.MmapBase.sv48_band_is_linux_set] is the
    same shape for the base band alone. *)
Theorem entry_launch_ok_va_is_linux : forall v en inp,
  entry_launch_ok_va v en inp
  <-> exists k r' r q,
        linux_launch_state v inp k r' r q
          (bv_unsigned (ed_top (en_draw en)))
          (bv_unsigned (en_sp en))
          (bv_unsigned (en_mmap_base en)).
Proof.
  intros v [sp brk mbase draw] inp.
  cbn [entry_launch_ok_va en_sp en_brk en_mmap_base en_draw].
  unfold linux_launch_state. cbv zeta.
  split.
  - intros (Htop & Hsp & Hbase).
    destruct (linux_stack_top_complete v (kb_aslr (in_kernel inp))
                (ed_top draw) Htop) as (k & r' & Hk & Hk0 & Hr' & Htopv).
    destruct (linux_entry_sp_complete (ed_top draw) sp inp Hsp)
      as (r & Hr & Hspv).
    destruct Hbase as (q & Hq0 & Hqlt & Hq00 & Hbv).
    exists k, r', r, q.
    split; [exact Hk|]. split; [exact Hk0|]. split; [exact Hr'|].
    split; [exact Hr|]. split; [exact Hq0|]. split; [exact Hqlt|].
    split; [exact Hq00|]. split; [exact Htopv|].
    split; [exact Hspv|]. exact Hbv.
  - intros (k & r' & r & q &
            Hk & Hk0 & Hr' & Hr & Hq0 & Hqlt & Hq00 & Htopv & Hspv & Hbv).
    split; [|split].
    + exact (linux_stack_top_sound v (kb_aslr (in_kernel inp)) (ed_top draw)
               k r' Hk Hk0 Hr' Htopv).
    + exact (linux_entry_sp_sound (ed_top draw) sp inp r Hr Hspv).
    + exists q. split; [exact Hq0|]. split; [exact Hqlt|].
      split; [exact Hq00|]. exact Hbv.
Qed.

(* ========================================================================= *)
(** ** The fixture                                                           *)
(* ========================================================================= *)

(** argv ["a"] and the exec file name "a": one byte each, 'a' = 97.
    [State.default_execfn] is the same name, so a positional
    [State.mkProcInput] literal launches under it too. *)
Definition a1_argv : list (list byte) := [[Z_to_bv 8 97]].
Definition a1_execfn : list byte := [Z_to_bv 8 97].

(** The launch facts: no transparent huge pages, the FIRST vDSO image
    ([kb_vdso] 0, one text page under [State.vdso_text_pages]), the
    guard gap at its boot default of 256 pages (mm/mmap.c,
    [stack_guard_gap = 256UL << PAGE_SHIFT]), [vm.mmap_rnd_bits] at
    riscv64's ARCH_MMAP_RND_BITS_MIN of 18 ([kb_rnd_bits] 0,
    arch/riscv/Kconfig), CONFIG_RSEQ on, no vector unit and no cache
    leaf reported.  Randomization is the one fact the examples vary. *)
Definition a1_kernel (aslr : bool) : KernelBuild :=
  mkKernelBuild false 0%N aslr 256%N 0%N true 0%N cache_view_absent.

Definition a1_input_argv (argv : list (list byte)) (execfn : list byte)
    (kb : KernelBuild) : ProcInput :=
  mkProcInput_full argv [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1000) []
                   net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc
                   false Sv48 default_urandom [] kb execfn true true false.

(** The fixture's input with the launch facts left open, so that a
    refusal below can be stated for EVERY value of them. *)
Definition a1_input_kb (kb : KernelBuild) : ProcInput :=
  a1_input_argv a1_argv a1_execfn kb.

Definition a1_input (aslr : bool) : ProcInput := a1_input_kb (a1_kernel aslr).

(** The three measurements the spec's "The block" names for this
    fixture, read off [StackLayout]'s own definitions: the vector is 29
    entries, [items] is 4, C = 512 and L = 4. *)
Example a1_fixture_measurements :
  auxv_count true = 29%nat
  /\ block_items a1_argv [] = 4%nat
  /\ block_head_size true a1_argv [] = 512%nat
  /\ launch_string_bytes a1_argv [] a1_execfn = 4%nat.
Proof. repeat split. Qed.

Example a1_mmap_rnd_bits_is_18 : mmap_rnd_bits Sv48 (a1_kernel true) = 18.
Proof. reflexivity. Qed.

(** The AT_RANDOM draw: sixteen distinct bytes, 0x00 to 0x0f from the
    bottom, so the block example below pins WHERE they land and not
    only that they are there. *)
Definition a1_random : bv 128 := Z_to_bv 128 0x0f0e0d0c0b0a09080706050403020100.

Definition a1_draw (top : Z) : EntryDraw :=
  mkDraw a1_random (Z_to_bv 64 top) vdso_keeps_all.

Definition a1_entry (sp mbase top : Z) : ExecEntry :=
  mkEntry (Z_to_bv 64 sp) (Z_to_bv 64 0) (Z_to_bv 64 mbase) (a1_draw top).

Local Lemma bvu : forall z,
  0 <= z < 18446744073709551616 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z H. apply bv_unsigned_Z_to_bv_u64.
  unfold two_pow_64. change (2 ^ 64) with 18446744073709551616. exact H.
Qed.

(* ========================================================================= *)
(** ** The admitted entries                                                  *)
(* ========================================================================= *)

(** WITHOUT RANDOMIZATION there is one stack top the unraced launch
    gives — STACK_TOP itself — one stack pointer at the top of rule 2,
    and one base: the gap is [max(128 MiB, 8 MiB + 1 MiB)] = 128 MiB
    and nothing is drawn, so the base is STACK_TOP - 128 MiB. *)
Example a1_no_aslr_admitted :
  entry_launch_ok_va Sv48
    (a1_entry 0x7ffffffffdf0 0x7ffff8000000 0x800000000000) (a1_input false).
Proof.
  cbn [entry_launch_ok_va a1_entry a1_draw en_draw ed_top].
  split; [|split].
  - unfold valid_stack_top_va. rewrite (bvu 0x800000000000 ltac:(lia)).
    repeat split; vm_compute; congruence.
  - unfold valid_launch_sp. rewrite (bvu 0x7ffffffffdf0 ltac:(lia)).
    repeat split; vm_compute; congruence.
  - exists 0. split; [lia|]. split; [intros Hc; discriminate Hc|].
    split; [intros _; reflexivity|].
    rewrite (bvu 0x7ffff8000000 ltac:(lia)). vm_compute. reflexivity.
Qed.

(** WITH RANDOMIZATION at the far end of every draw: the stack page
    draw at 0x3ffff pages and the [setup_arg_pages] pad at its largest,
    so the top is STACK_TOP - 2^30; the [create_elf_tables] pad at its
    largest, so the stack pointer is at the BOTTOM of rule 2's
    interval; and the mmap draw at 0, the highest base of the
    randomized launch. *)
Example a1_aslr_admitted_base_hi :
  entry_launch_ok_va Sv48
    (a1_entry 0x7fffbfffedf0 0x7fffbf701000 0x7fffc0000000) (a1_input true).
Proof.
  cbn [entry_launch_ok_va a1_entry a1_draw en_draw ed_top].
  split; [|split].
  - unfold valid_stack_top_va. rewrite (bvu 0x7fffc0000000 ltac:(lia)).
    repeat split; vm_compute; congruence.
  - unfold valid_launch_sp. rewrite (bvu 0x7fffbfffedf0 ltac:(lia)).
    repeat split; vm_compute; congruence.
  - exists 0. split; [lia|]. split; [intros _; vm_compute; congruence|].
    split; [intros Hc; discriminate Hc|].
    rewrite (bvu 0x7fffbf701000 ltac:(lia)). vm_compute. reflexivity.
Qed.

(** …and the same launch with the mmap draw at its largest, 2^18 - 1
    pages at [vm.mmap_rnd_bits] 18: the lowest base this machine
    gives. *)
Example a1_aslr_admitted_base_lo :
  entry_launch_ok_va Sv48
    (a1_entry 0x7fffbfffedf0 0x7fff7f702000 0x7fffc0000000) (a1_input true).
Proof.
  cbn [entry_launch_ok_va a1_entry a1_draw en_draw ed_top].
  split; [|split].
  - unfold valid_stack_top_va. rewrite (bvu 0x7fffc0000000 ltac:(lia)).
    repeat split; vm_compute; congruence.
  - unfold valid_launch_sp. rewrite (bvu 0x7fffbfffedf0 ltac:(lia)).
    repeat split; vm_compute; congruence.
  - exists 262143. split; [lia|]. split; [intros _; vm_compute; congruence|].
    split; [intros Hc; discriminate Hc|].
    rewrite (bvu 0x7fff7f702000 ltac:(lia)). vm_compute. reflexivity.
Qed.

(* ========================================================================= *)
(** ** The four kinds of state no launch gives                               *)
(* ========================================================================= *)

(** A BASE OF STACK_TOP - 128 MiB MEANS THE LAUNCH DID NOT RANDOMIZE.
    Under PF_RANDOMIZE [mmap_base] (mm/util.c) adds
    [STACK_RND_MASK << PAGE_SHIFT] to the gap, and the guard gap is at
    most 0x4aba6a2ab000 bytes ([State.stack_guard_gap_bytes]), so the
    sum never wraps and the clamp never lowers it: the gap is at least
    0x407ff000 and every randomized base is at most
    STACK_TOP - 0x407ff000 = 0x7fffbf801000.  True for every value of
    the launch facts, which is why the pair below is refused for every
    one of them. *)
Local Lemma mmap_gap_sv48_aslr_lb : forall kb,
  kb_aslr kb = true -> 0x407ff000 <= mmap_gap Sv48 kb.
Proof.
  intros kb Ha. unfold mmap_gap. rewrite Ha. cbv zeta.
  pose proof (stack_guard_gap_bytes_bounds kb) as Hg.
  unfold stack_max_size, stack_rnd_max, mmap_min_gap, mmap_max_gap,
         two_pow_64 in *.
  cbn [va_stack_top].
  unfold sp_window_hi.
  change (2 ^ 64) with 18446744073709551616.
  rewrite Z.mod_small by lia.
  destruct (Z.gtb_spec (8 * 1024 * 1024 + (stack_guard_gap_bytes kb + 0x3ffff000))
                       (8 * 1024 * 1024)) as [Hov|Hov]; [|lia].
  cbn [andb].
  destruct (Z.ltb_spec (8 * 1024 * 1024 + (stack_guard_gap_bytes kb + 0x3ffff000))
                       (128 * 1024 * 1024)) as [Hmin|Hmin]; [lia|].
  cbn [andb].
  destruct (Z.gtb_spec (8 * 1024 * 1024 + (stack_guard_gap_bytes kb + 0x3ffff000))
                       (0x800000000000 / 6 * 5)) as [Hmax|Hmax]; [|lia].
  vm_compute (0x800000000000 / 6 * 5). lia.
Qed.

Local Lemma a1_base_fixed_forces_no_aslr : forall kb (mbase : word),
  bv_unsigned mbase = 0x7ffff8000000 ->
  valid_launch_base Sv48 kb mbase -> kb_aslr kb = false.
Proof.
  intros kb mbase Hval (q & Hq0 & Hqlt & Hq00 & Hbv).
  destruct (kb_aslr kb) eqn:Ha; [|reflexivity]. exfalso.
  pose proof (mmap_gap_sv48_aslr_lb kb Ha) as Hgap.
  rewrite Hval in Hbv. unfold mmap_base_of in Hbv.
  assert (Hle : page_round_up_Z (va_stack_top Sv48 - mmap_gap Sv48 kb
                                 - page_size * q) <= 0x7fffbf801000).
  { apply page_round_up_Z_le; [reflexivity|].
    cbn [va_stack_top]. unfold sp_window_hi, page_size in *. lia. }
  lia.
Qed.

(** A stack top the launch can give is at most one page below
    STACK_TOP when the launch did not randomize, so it is one of two
    values. *)
Local Lemma a1_top_no_aslr : forall (top : word),
  valid_stack_top_va Sv48 false top ->
  bv_unsigned top = 0x800000000000 \/ bv_unsigned top = 0x7ffffffff000.
Proof.
  intros top (Hmod & Hhi & Hlo).
  cbn [va_stack_top] in Hhi, Hlo. unfold sp_window_hi, page_size in *.
  Z.div_mod_to_equations. lia.
Qed.

(** …and under either randomization mode it is at least
    STACK_TOP - 2^30: the page draw is at most 0x3ffff pages and
    [arch_align_stack] takes at most one page more
    ([randomize_stack_top], mm/util.c; [setup_arg_pages],
    fs/exec.c). *)
Local Lemma a1_top_ge : forall aslr (top : word),
  valid_stack_top_va Sv48 aslr top -> 0x7fffc0000000 <= bv_unsigned top.
Proof.
  intros aslr top (_ & _ & Hlo).
  cbn [va_stack_top] in Hlo.
  unfold sp_window_hi, stack_rnd_max, page_size in Hlo.
  destruct aslr; lia.
Qed.

(** The bottom of rule 2 for this fixture, as a function of the stack
    top: the strings are 4 bytes and C is 512 with CONFIG_RSEQ, 480
    without, which are the only two values the launch facts can give
    it. *)
Local Lemma a1_sp_lo_ge : forall kb (top : word) u,
  bv_unsigned top = u -> u - 4634 <= launch_sp_lo top (a1_input_kb kb).
Proof.
  intros kb top u Hu. unfold launch_sp_lo.
  cbn [a1_input_kb a1_input_argv in_argv in_envp in_execfn in_kernel].
  rewrite Hu.
  replace (Z.of_nat (launch_string_bytes a1_argv [] a1_execfn)) with 4
    by reflexivity.
  pose proof (align_down16_ge (u - 8 - 4 - 4095)).
  destruct (kb_rseq kb);
    [ replace (Z.of_nat (block_head_size true a1_argv [])) with 512
        by reflexivity
    | replace (Z.of_nat (block_head_size false a1_argv [])) with 480
        by reflexivity ]; lia.
Qed.

(** The bottom of rule 2 at the two stack tops a launch with no page
    draw gives.  C is 512 with CONFIG_RSEQ and 480 without, and those
    are the only two values the launch facts can give it, so the lowest
    stack pointer of the raced range is 0x7fffffffdff0 - 512. *)
Local Lemma a1_sp_lo_value : forall kb (top : word) u,
  bv_unsigned top = u ->
  launch_sp_lo top (a1_input_kb kb)
  = align_down16 (u - 4107)
    - Z.of_nat (block_head_size (kb_rseq kb) a1_argv []).
Proof.
  intros kb top u Hu. unfold launch_sp_lo.
  cbn [a1_input_kb a1_input_argv in_argv in_envp in_execfn in_kernel].
  rewrite Hu.
  replace (Z.of_nat (launch_string_bytes a1_argv [] a1_execfn)) with 4
    by reflexivity.
  replace (u - 8 - 4 - 4095) with (u - 4107) by ring.
  reflexivity.
Qed.

Local Lemma a1_C_le : forall b,
  Z.of_nat (block_head_size b a1_argv []) <= 512.
Proof.
  destruct b;
    [ replace (Z.of_nat (block_head_size true a1_argv [])) with 512
        by reflexivity
    | replace (Z.of_nat (block_head_size false a1_argv [])) with 480
        by reflexivity ]; lia.
Qed.

Local Lemma ad16_top0 : align_down16 (0x800000000000 - 4107) = 0x7fffffffeff0.
Proof. vm_compute. reflexivity. Qed.

Local Lemma ad16_top1 : align_down16 (0x7ffffffff000 - 4107) = 0x7fffffffdff0.
Proof. vm_compute. reflexivity. Qed.

(** THE BOTTOM OF THE RACED RANGE IS 0x7fffffffddf0, whichever of the
    two tops the launch got and whichever value CONFIG_RSEQ has. *)
Local Lemma a1_sp_lo_raced_min : forall kb (top : word),
  (bv_unsigned top = 0x800000000000 \/ bv_unsigned top = 0x7ffffffff000) ->
  0x7fffffffddf0 <= launch_sp_lo top (a1_input_kb kb).
Proof.
  intros kb top Hu.
  pose proof (a1_sp_lo_value kb top (bv_unsigned top) eq_refl) as Hval.
  pose proof (a1_C_le (kb_rseq kb)) as HC.
  destruct Hu as [Hu|Hu]; rewrite Hu in Hval.
  - rewrite ad16_top0 in Hval. lia.
  - rewrite ad16_top1 in Hval. lia.
Qed.

(** KIND 1, THE PAIR.  sp = 0x7fffe0000000 with base = 0x7ffff8000000
    satisfied the old [Run.valid_entry].  The base says the launch did
    not randomize, and then the stack top is STACK_TOP or one page
    below it, so the stack pointer cannot be 0x1ffffdf0 bytes under
    it.  Refused for every stack top and every value of the launch
    facts. *)
Lemma a1_kind1_pair_refused : forall kb brk (sp mbase : word) rnd vd (top : word),
  bv_unsigned sp = 0x7fffe0000000 ->
  bv_unsigned mbase = 0x7ffff8000000 ->
  ~ entry_launch_ok_va Sv48 (mkEntry sp brk mbase (mkDraw rnd top vd))
      (a1_input_kb kb).
Proof.
  intros kb brk sp mbase rnd vd top Hsp Hmb (Htop & Hspok & Hbase).
  cbn [en_draw ed_top] in Htop, Hspok.
  assert (Ha : kb_aslr kb = false)
    by exact (a1_base_fixed_forces_no_aslr kb mbase Hmb Hbase).
  assert (Htop' : valid_stack_top_va Sv48 false top)
    by (rewrite <- Ha; exact Htop).
  destruct Hspok as (_ & Hlo & _).
  pose proof (a1_sp_lo_ge kb top (bv_unsigned top) eq_refl) as Hge.
  destruct (a1_top_no_aslr top Htop') as [Hu|Hu]; rewrite Hu in Hge; lia.
Qed.

(** KIND 2, sp ALONE.  [State.sp_window_lo] is 2^47 - 2 GiB, and
    0x7fff80000000 is that floor.  The lowest stack top any launch
    gives is STACK_TOP - 2^30, so the lowest stack pointer is about
    0x7fffbfffe000: refused for every stack top, every base and every
    value of the launch facts, the base 0x154555557000 of
    [State.mmap_base_min] included. *)
Lemma a1_kind2_sp_refused : forall kb brk (sp mbase : word) rnd vd (top : word),
  bv_unsigned sp = 0x7fff80000000 ->
  bv_unsigned mbase = 0x154555557000 ->
  ~ entry_launch_ok_va Sv48 (mkEntry sp brk mbase (mkDraw rnd top vd))
      (a1_input_kb kb).
Proof.
  intros kb brk sp mbase rnd vd top Hsp Hmb (Htop & Hspok & _).
  cbn [en_draw ed_top] in Htop, Hspok.
  destruct Hspok as (_ & Hlo & _).
  pose proof (a1_sp_lo_ge kb top (bv_unsigned top) eq_refl) as Hge.
  pose proof (a1_top_ge _ top Htop) as Htge.
  lia.
Qed.

(** THE BOTTOM OF THE RACED RANGE.  Without randomization the stack
    pointer can still be two pages below the unraced launch's, because
    [arch_align_stack] reads [randomize_va_space] again; the lowest it reaches is
    0x7fffffffddf0.  Sixteen bytes below that is no launch, for every
    stack top and every value of the launch facts with randomization
    off. *)
Lemma a1_sp_below_raced_range_refused :
  forall kb brk (sp mbase : word) rnd vd (top : word),
  kb_aslr kb = false ->
  bv_unsigned sp = 0x7fffffffdde0 ->
  bv_unsigned mbase = 0x7ffff8000000 ->
  ~ entry_launch_ok_va Sv48 (mkEntry sp brk mbase (mkDraw rnd top vd))
      (a1_input_kb kb).
Proof.
  intros kb brk sp mbase rnd vd top Ha Hsp Hmb (Htop & Hspok & _).
  cbn [en_draw ed_top] in Htop, Hspok.
  assert (Htop' : valid_stack_top_va Sv48 false top)
    by (rewrite <- Ha; exact Htop).
  destruct Hspok as (_ & Hlo & _).
  pose proof (a1_sp_lo_raced_min kb top (a1_top_no_aslr top Htop')) as Hmin.
  lia.
Qed.

(** KIND 5, BASES OF DIFFERENT MACHINES.  One launch has one
    randomization mode, so the fixture's base without randomization is
    no base of the fixture WITH it, and the other way round.  Refused
    for every stack pointer and every stack top. *)
Lemma a1_kind5_base_with_aslr_refused :
  forall brk (sp mbase : word) rnd vd (top : word),
  bv_unsigned mbase = 0x7ffff8000000 ->
  ~ entry_launch_ok_va Sv48 (mkEntry sp brk mbase (mkDraw rnd top vd))
      (a1_input true).
Proof.
  intros brk sp mbase rnd vd top Hmb (_ & _ & Hbase).
  assert (Ha : kb_aslr (a1_kernel true) = false)
    by exact (a1_base_fixed_forces_no_aslr (a1_kernel true) mbase Hmb Hbase).
  discriminate Ha.
Qed.

Lemma a1_kind5_base_without_aslr_refused :
  forall brk (sp mbase : word) rnd vd (top : word),
  bv_unsigned mbase = 0x7fffbf701000 ->
  ~ entry_launch_ok_va Sv48 (mkEntry sp brk mbase (mkDraw rnd top vd))
      (a1_input false).
Proof.
  intros brk sp mbase rnd vd top Hmb (_ & _ & (q & Hq0 & _ & Hq00 & Hbv)).
  rewrite (Hq00 eq_refl) in Hbv. rewrite Hmb in Hbv.
  vm_compute in Hbv. discriminate Hbv.
Qed.

(** THE EDGES OF RULE 1.  One page below the lowest randomized top is
    a page no [randomize_stack_top] draw and no [arch_align_stack] pad
    reach, and so is the second page below STACK_TOP without
    randomization. *)
Lemma a1_top_below_range_refused :
  forall brk (sp mbase : word) rnd vd (top : word),
  bv_unsigned top = 0x7fffbffff000 ->
  ~ entry_launch_ok_va Sv48 (mkEntry sp brk mbase (mkDraw rnd top vd))
      (a1_input true).
Proof.
  intros brk sp mbase rnd vd top Htv (Htop & _ & _).
  pose proof (a1_top_ge _ top Htop) as Hge. lia.
Qed.

Lemma a1_top_two_pages_down_refused :
  forall brk (sp mbase : word) rnd vd (top : word),
  bv_unsigned top = 0x7fffffffe000 ->
  ~ entry_launch_ok_va Sv48 (mkEntry sp brk mbase (mkDraw rnd top vd))
      (a1_input false).
Proof.
  intros brk sp mbase rnd vd top Htv (Htop & _ & _).
  destruct (a1_top_no_aslr top Htop) as [Hu|Hu]; rewrite Htv in Hu;
    discriminate Hu.
Qed.

(* ========================================================================= *)
(** ** KIND 4: launches Linux refuses                                        *)
(* ========================================================================= *)

Local Lemma length_flatten_repeat : forall (s : list byte) n,
  length (flatten_strings (repeat s n)) = (n * (length s + 1))%nat.
Proof.
  intros s n. induction n as [|n IH]; [reflexivity|].
  cbn [repeat flatten_strings flat_map]. rewrite length_app.
  change (flat_map (fun s0 : list byte => s0 ++ [Z_to_bv 8 0]) (repeat s n))
    with (flatten_strings (repeat s n)).
  rewrite IH, length_app. cbn [length]. lia.
Qed.

(** 16 arguments of 131071 bytes are 2 MiB with their NULs, and the
    pointer array costs 128 bytes more.  [bprm_stack_limits]
    (fs/exec.c) leaves 2 MiB at the 8 MiB stack limit, so Linux refuses
    this launch with -E2BIG while [Run.valid_argv]'s own bound admits
    it: that is the joint bound [Run.valid_launch] adds.

    The lengths are written through [Z.to_nat] so that the numbers stay
    binary: a [nat] literal this large elaborates to [Nat.of_num_uint]
    of its digits, which [lia] cannot see through. *)
Definition a1_big_arg : list byte := repeat (Z_to_bv 8 97) (Z.to_nat 131071).
Definition a1_big_argv : list (list byte) := repeat a1_big_arg (Z.to_nat 16).

Lemma a1_e2big_argv_refused :
  ~ valid_launch (a1_input_argv a1_big_argv a1_execfn (a1_kernel true)).
Proof.
  intros (_ & Hle).
  unfold launch_bytes, launch_string_bytes, e2big_limit in Hle.
  cbn [a1_input_argv in_argv in_envp in_execfn] in Hle.
  unfold a1_big_argv, a1_big_arg, a1_execfn in Hle.
  rewrite length_flatten_repeat, !repeat_length in Hle.
  cbn [flatten_strings flat_map length] in Hle.
  lia.
Qed.

(** The EMPTY exec file name is not a name [getname_flags] (fs/namei.c)
    can return: it refuses it without AT_EMPTY_PATH, and with
    AT_EMPTY_PATH and AT_FDCWD the open finds a directory, which
    [may_open] refuses for exec. *)
Lemma a1_empty_execfn_refused :
  ~ valid_launch (a1_input_argv a1_argv [] (a1_kernel true)).
Proof.
  intros (Hfn & _).
  cbn [a1_input_argv in_execfn] in Hfn.
  destruct Hfn as [[Hlen _] | [[ds [Heq _]] | [ds [rest [Heq _]]]]].
  - cbn [length] in Hlen. lia.
  - cbn [dev_fd_prefix app] in Heq. discriminate Heq.
  - cbn [dev_fd_prefix app] in Heq. discriminate Heq.
Qed.

(* ========================================================================= *)
(** ** The block of the first admitted entry                                 *)
(* ========================================================================= *)

(** The image the block publishes: a phdr table at 0x10040 with four
    56-byte entries, and an entry point of 0x10100. *)
Definition a1_phdr : PhdrInfo := mkPhdrInfo 0x10040%N 56%N 4%N.
Definition a1_img_entry : word := Z_to_bv 64 0x10100.

Definition a1_block : list byte :=
  entry_stack_image (a1_input false) (Z_to_bv 64 0x7ffff8000000) a1_phdr
    a1_img_entry (Z_to_bv 64 0x7ffffffffdf0) (a1_draw 0x800000000000).

(** An eight-byte little-endian word of the block, by byte offset from
    sp, and the auxv read out of those words. *)
Definition le8_at (bs : list byte) (off : nat) : Z :=
  fold_right (fun b acc => acc * 256 + bv_unsigned b) 0 (firstn 8 (skipn off bs)).

Definition auxv_read (bs : list byte) (off n : nat) : list (Z * Z) :=
  map (fun i => (le8_at bs (off + 16 * i)%nat, le8_at bs (off + 16 * i + 8)%nat))
      (seq 0 n).

(** The eight bytes of a word, bottom byte first: the serialization
    [StackLayout.build_stack_bytes] uses ([BvBase.word_le8]), written
    out here so the expected block below is literal numbers. *)
Definition w8 (x : Z) : list Z :=
  [x mod 256; x / 256 mod 256; x / 65536 mod 256; x / 16777216 mod 256;
   x / 4294967296 mod 256; x / 1099511627776 mod 256;
   x / 281474976710656 mod 256; x / 72057594037927936 mod 256].

(** THE AUXILIARY VECTOR THIS LAUNCH PUBLISHES, computed by hand from
    the spec's "The block" and Design "The vDSO pages":

    - AT_SYSINFO_EHDR (33) is the vDSO text, directly below the mmap
      base.  Its length is now MEASURED rather than a formula over a
      free field: [State.vdso_text_pages] is the page count of the
      image [kb_vdso] names in [Vdso.vdso_images], and the entry
      [default_kernel] names is the riscv64 defconfig build of
      v6.18.46 (commit 1f99e9ab748f), 5704 bytes and so TWO pages.
      The base is 0x7ffff8000000 - 2 * 4096.
    - the eight cache words (40 to 47) are 0: no leaf is reported, so
      [get_cache_size] and [get_cache_geometry]
      (arch/riscv/kernel/cacheinfo.c) find nothing.
    - AT_MINSIGSTKSZ (51) is [round_up(F + V, 16)] with F = 1088 the
      size of [struct rt_sigframe] and V = 0 with no vector unit
      (arch/riscv/kernel/signal.c, [get_rt_frame_size]).
    - AT_HWCAP (16) is the mask without V, AT_PAGESZ (6) is 4096 and
      AT_CLKTCK (17) is USER_HZ = 100.
    - AT_PHDR (3), AT_PHENT (4), AT_PHNUM (5) come from the image.
    - AT_BASE (7) and AT_FLAGS (8) are 0, AT_ENTRY (9) is the image's
      entry.
    - AT_UID (11), AT_EUID (12), AT_GID (13), AT_EGID (14) are 1000 and
      AT_SECURE (23) is 0.
    - AT_RANDOM (25) is sp + C - 16 = 0x7ffffffffdf0 + 496, and
      AT_EXECFN (31) is the exec name at the top of the string area,
      [ed_top] - 8 - 1 - 1.
    - AT_RSEQ_FEATURE_SIZE (27) is [offsetof(struct rseq, end)] = 28
      and AT_RSEQ_ALIGN (28) is 32 (include/uapi/linux/rseq.h).
    - AT_NULL (0) closes it. *)
Definition a1_expected_auxv : list (Z * Z) :=
  [ (33, 0x7ffff7ffe000);
    (40, 0); (41, 0); (42, 0); (43, 0); (44, 0); (45, 0); (46, 0); (47, 0);
    (51, 1088);
    (16, 0x112D); (6, 4096); (17, 100);
    (3, 0x10040); (4, 56); (5, 4);
    (7, 0); (8, 0); (9, 0x10100);
    (11, 1000); (12, 1000); (13, 1000); (14, 1000); (23, 0);
    (25, 0x7fffffffffe0); (31, 0x7ffffffffff6);
    (27, 28); (28, 32);
    (0, 0) ].

(** The block runs from sp to the stack VMA's end and nowhere else:
    0x800000000000 - 0x7ffffffffdf0 = 528 bytes, which is
    C + pad + L + 8 = 512 + 4 + 4 + 8. *)
Example a1_block_length : length a1_block = 528%nat.
Proof. vm_compute. reflexivity. Qed.

(** The three addresses the auxv and the pointer array carry, each
    computed from [StackLayout]'s own definition and checked against
    the layout: the lowest string byte is [ed_top] - 8 - L, the exec
    name sits at the top of the string area, and the sixteen AT_RANDOM
    bytes end where the strings' pad begins. *)
Example a1_block_addresses :
  bv_unsigned (string_base_addr (Z_to_bv 64 0x800000000000) a1_argv []
                                a1_execfn) = 0x7ffffffffff4
  /\ bv_unsigned (at_execfn_ptr (Z_to_bv 64 0x800000000000) a1_execfn)
     = 0x7ffffffffff6
  /\ bv_unsigned (at_random_ptr (Z_to_bv 64 0x7ffffffffdf0) true a1_argv [])
     = 0x7fffffffffe0
  /\ block_pad_len true (Z_to_bv 64 0x7ffffffffdf0) (Z_to_bv 64 0x800000000000)
                   a1_argv [] a1_execfn = 4%nat.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** argc at sp, the one argv pointer at sp + 8, then the argv array's
    NULL and the envp array's NULL. *)
Example a1_block_head_words :
  le8_at a1_block 0 = 1
  /\ le8_at a1_block 8 = 0x7ffffffffff4
  /\ le8_at a1_block 16 = 0
  /\ le8_at a1_block 24 = 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** The whole vector, read out of the block's bytes at sp + 8 * items:
    twenty-nine (type, value) pairs. *)
Example a1_block_auxv_is_linuxs :
  auxv_read a1_block 32 29 = a1_expected_auxv.
Proof. vm_compute. reflexivity. Qed.

(** AND THE WHOLE BLOCK, byte for byte: argc and the two pointer
    arrays, the vector, no alignment gap ([items] is 4, so
    [STACK_ROUND] removes nothing), the sixteen AT_RANDOM bytes of this
    draw, the four-byte [arch_align_stack] pad, "a\0a\0" — argv[0] then
    the exec name — and the eight-byte slot [create_init_stack_vma]
    (mm/vma_exec.c) skipped at the stack VMA's end. *)
Example a1_block_is_linuxs_bytes :
  map bv_unsigned a1_block
  = w8 1 ++ w8 0x7ffffffffff4 ++ w8 0 ++ w8 0
    ++ flat_map (fun tv => w8 (fst tv) ++ w8 (snd tv)) a1_expected_auxv
    ++ [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]
    ++ [0; 0; 0; 0]
    ++ [97; 0; 97; 0]
    ++ [0; 0; 0; 0; 0; 0; 0; 0].
Proof. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(** ** Every valid input still has an entry                                  *)
(* ========================================================================= *)

Local Lemma a1_nul_free : ~ In (Z_to_bv 8 0) [Z_to_bv 8 97].
Proof.
  cbn [In]. intros [H | []].
  apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate H.
Qed.

Local Lemma a1_valid_argv : valid_argv a1_argv.
Proof.
  unfold valid_argv, a1_argv, total_arg_bytes.
  cbn [length fold_right tl].
  split; [lia|]. split; [lia|].
  split; [apply Forall_cons; [cbn [length]; lia | apply Forall_nil]|].
  split; [apply Forall_cons; [exact a1_nul_free | apply Forall_nil]|].
  apply Forall_nil.
Qed.

Local Lemma a1_valid_envp : valid_envp (@nil (list byte)).
Proof.
  unfold valid_envp, total_arg_bytes. cbn [length fold_right].
  split; [lia|]. split; [lia|]. split; apply Forall_nil.
Qed.

Local Lemma a1_valid_launch : forall aslr, valid_launch (a1_input aslr).
Proof.
  intros aslr. unfold valid_launch. split.
  - left. unfold valid_path_name. cbn [a1_input a1_input_kb a1_input_argv
                                       in_execfn a1_execfn length].
    split; [lia|]. exact a1_nul_free.
  - unfold launch_bytes, e2big_limit.
    cbn [a1_input a1_input_kb a1_input_argv in_argv in_envp in_execfn].
    vm_compute. congruence.
Qed.

(** THE QUANTIFIER IS NOT EMPTY.  [Run.launch_entry_va] fired on the
    fixture: the stack at STACK_TOP, the stack pointer at the top of
    rule 2 and the mmap base of rule 3 with no draw.  The break is 0,
    which [Run.valid_brk] admits for an image with no reservations. *)
Example a1_witness_entry_is_valid :
  valid_entry_va Sv48 (mkImage [] 0%N a1_phdr)
    (launch_entry_va Sv48 (a1_input true) (Z_to_bv 64 0) a1_random
                     vdso_keeps_all)
    (a1_input true).
Proof.
  apply launch_entry_va_valid.
  - exact a1_valid_argv.
  - exact a1_valid_envp.
  - exact (a1_valid_launch true).
  - unfold valid_brk.
    (* [segments_reserved] now filters the kernel's own mappings out, and
       [cbn] with a delta list does not reduce through the filter here, so
       the empty image's reservations are replaced by computation. *)
    replace (segments_reserved ([] : list Segment)) with (@nil (word * word))
      by reflexivity.
    cbn [reserved_top].
    rewrite (bvu 0 ltac:(lia)). unfold brk_aslr_max, page_size.
    repeat split; lia.
Qed.
