(** * LinuxProcessSem.Checks.Cases.Prelude — worked examples for the shared helpers

    Shared infrastructure for the worked examples below it: this one
    mirrors no kernel source, and holds nothing syscall-specific.

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

(** [vm_compute]-normalized results can differ from literal expected
    values only in the (opaque, proof-irrelevant) [BvWf] proofs inside
    [bv] leaves; descend to those leaves and compare unsigned values. *)
Ltac check_eq :=
  vm_compute;
  repeat first [reflexivity | (apply bv_eq; reflexivity) | progress f_equal].

(* =========================================================================
   PART 1 — the EQUIVALENCE definition, on synthetic behaviors

   Trace sets written down by hand, so [Equivalence.equiv]'s verdicts can
   be read off without running a binary.  Per-binary versions of these
   (deriving the trace sets from actual RISC-V images) are the
   per-problem proofs under [Examples/].
   ========================================================================= *)

Definition demo_phdrs : PhdrInfo := mkPhdrInfo 0x10040 56 6.

(** The allocation budget ([State.vm_limit]) these demo checks run
    under: 1 GiB — far above every grant they make, so the budget gate
    is live but never the deciding conjunct except where a check says
    so explicitly (the exhaustion checks below). *)

Definition demo_limit : Z := 0x40000000%Z.

(** The stack pointer these demo checks are started with: the bottom of
    the SP window, so their grant top ([State.alloc_top]) is the lowest
    any admissible run has and every literal below is admitted by every
    run.  [demo_top] is that top, spelled once. *)
Definition demo_sp : word := Z_to_bv 64 sp_window_lo.
Definition demo_top : Z := (sp_window_lo - stack_max_size)%Z.

Lemma demo_top_is_alloc_top : forall reserved brk0 mbase lim inp,
  alloc_top (m_vmmaps (init_model reserved brk0 mbase demo_sp lim inp))
  = demo_top.
Proof. reflexivity. Qed.

(** The process input ([State.ProcInput]) the checks below run on: no
    arguments and no environment, because nothing below reads either.
    That leaves the file system and the standard-input stream, which a
    few checks do vary, as the only two things a call site states.
    Every check that needs no arguments goes through this name, so a new
    [State.ProcInput] field costs those call sites nothing.  The
    exceptions write [mkProcInput] out in full because they need a
    NONEMPTY argv, and they fall into two groups rather than being a list
    worth enumerating: the undecodable-image checks in part 1
    ([run_of_undecodable_image_is_unmodeled],
    [run_of_undecodable_image_refutes_modeled]), and every statement in
    part 6 of [Checks.Examples].  Part 6 needs a nonempty argv because
    [Run.valid_argv] requires at least one argument, so [Run.valid_input]
    is unprovable for the empty argv [demo_input] supplies, and
    [Checks.Examples.demo_input_valid] is where a one-element argv is
    discharged instead.  Part 6's statements that carry no validity
    premise of their own still spell it out, because what they need is
    the SAME input that lemma is about.
    Named as a rule rather than a list: the second group grows with every
    check that has to name part 6's input.

    The launching user is an ORDINARY one, not root, so every check
    below runs unprivileged — that is what makes
    [State.creds_privileged] false for them and keeps the privileged
    credential arms to the checks that build a root model by name.  The
    group is a DIFFERENT number from the user on purpose: a state where
    the two coincide cannot tell a [getgid] wired to [cr_uid] from one
    wired to [cr_gid].

    The accept queue is [State.net_silent]: every peer connects, sends
    nothing and closes.  A check that needs a connection with content
    names its own queue rather than varying this one. *)
Definition demo_uid : word := Z_to_bv 64 1000.
Definition demo_gid : word := Z_to_bv 64 1002.

(** The AT_HWCAP word the fixtures launch with.  [Run.valid_hwcap]
    admits two, and the fixtures take the one WITHOUT V — not because
    the model prefers it, but because these checks are about other
    things and the V-carrying mask would make every one of them a
    statement about vector dispatch.  The check that the other mask is
    equally admitted is [valid_hwcap_admits_both_masks] below, and the
    check that the pair is a pair is
    [the_two_hwcap_masks_are_distinct] beside it. *)
Definition demo_hwcap : word := hwcap_rv64gc.


(** A demo AT_RANDOM draw (the [ed_random] half of [Run.ExecEntry]'s [en_draw]).  Every one of
    the sixteen bytes it serializes to is DIFFERENT, and none of them is
    zero: a fixture whose bytes repeated, or which were all zero, could
    not tell a check that reads byte [k] of the block from one that
    reads byte [j], nor either from one that reads zeros.  Any [bv 128] is a draw the kernel
    can make ([Run.mi_random] carries no validity predicate), so the
    only thing a fixture value has to be is DISTINGUISHING. *)
Definition demo_random : bv 128 :=
  Z_to_bv 128 0x0f1e2d3c4b5a69788796a5b4c3d2e1f0.

(** The stack VMA's end these fixtures launch with
    ([StackLayout.ed_top]): one page above [demo_sp].
    [setup_arg_pages] (fs/exec.c, Linux v6.18.46, commit 1f99e9ab748f)
    page-aligns the top, and the block now runs from the entry stack
    pointer UP TO it, so the whole entry image of these fixtures is
    4096 bytes — small enough for every check below to be a
    [vm_compute] over a literal list, which is why the fixture does not
    take the top at [State.sp_window_hi]. *)
Definition demo_stack_top : word := Z_to_bv 64 (sp_window_lo + page_size).

(** The two draws, and the all-zero one.  [ed_vdso] is
    [Run.vdso_keeps_all] in both: no check here runs a vDSO call, and
    that choice is one Linux can make (a vDSO function that writes only
    its result). *)
Definition demo_draw : EntryDraw :=
  mkDraw demo_random demo_stack_top vdso_keeps_all.
Definition zero_draw : EntryDraw :=
  mkDraw (Z_to_bv 128 0) demo_stack_top vdso_keeps_all.

(** THREE supplementary groups, ascending, and none of them 3.  The
    number [getgroups] reports is the LENGTH of this list, so a fixture
    whose length coincided with one of its elements — or with a uid, a
    gid, or the size argument a check passes — could not tell the model
    that counts from one that reports a member.  Ascending because that
    is the order the kernel stores ([groups_sort] runs inside
    [setgroups], and [groups_to_user] copies the stored order out), so
    this is a list a real [struct group_info] could hold. *)
Definition demo_groups : list word :=
  [Z_to_bv 64 27; Z_to_bv 64 1002; Z_to_bv 64 4000].

Definition demo_input (fs0 : Fs.Fs) (stdin0 : InputStream) : ProcInput :=
  mkProcInput [] [] fs0 stdin0 demo_uid demo_gid demo_groups net_silent
              default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

(** The same, with a DECLARED PRIVATE /tmp beside the image
    ([State.in_tmp]): the entries are keyed by their one component, and
    [State.init_model] seeds them under "/tmp/" ([State.fs_seed_tmp]).
    [demo_input] is this one with the empty declaration, which
    [State.fs_seed_tmp_nil] makes the image itself. *)
Definition demo_input_tmp (fs0 tmp0 : Fs.Fs) (stdin0 : InputStream)
    : ProcInput :=
  mkProcInput_full [] [] fs0 stdin0 demo_uid demo_gid demo_groups
                   net_silent default_nofile (Z_to_bv 64 0) demo_hwcap false
                   Sv48 default_urandom tmp0 default_kernel default_execfn
                   true true.

(** The launch facts the entry-block checks below read: the run's
    [mm->mmap_base], the [StackLayout.LaunchAuxv] the model derives
    from the declared kernel build at that base ([Run.launch_auxv]),
    and the one-argument input whose block they lay out.  One name
    each, so a check states a layout and not a derivation. *)
Definition demo_mbase : word := Z_to_bv 64 mmap_base_max.
Definition demo_la : LaunchAuxv := launch_auxv (demo_input [] IEof) demo_mbase.
Definition demo_pc : N := 0x10000%N.
Definition demo_argv : list (list byte) := [[Z_to_bv 8 120]].   (* "x" *)

Definition demo_x_input : ProcInput :=
  mkProcInput demo_argv [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

(** The credentials [demo_input] produces: an ordinary user whose real,
    effective and saved ids all agree, because [State.init_model] derives
    the effective and saved ones from the real one it is given. *)
Definition demo_creds : Creds :=
  mkCreds demo_uid demo_uid demo_uid demo_gid demo_gid demo_gid demo_groups.

(** So the very first step of this image is the model giving up — NOT a
    fault: the fetch itself succeeds. *)

Lemma iovcnt32_small : forall w, (bv_unsigned w <= IOV_MAX)%Z -> iovcnt32 w = w.
Proof.
  intros w H. unfold iovcnt32, abi_low32. rewrite Z.mod_small.
  - apply Z_to_bv_bv_unsigned.
  - pose proof (word_unsigned_range w) as Hr. unfold IOV_MAX in H.
    change (2 ^ 32)%Z with 4294967296%Z. split; lia.
Qed.

(** Any admissible ALL-READABLE channel-writev outcome leaves the
    model unchanged and delivers a NONEMPTY — possibly short — prefix
    of the gathered bytes: the return is the delivered length and the
    events are one [WriteEv] per delivered byte.  These are exactly the
    deliveries a [write] of the flat buffer admits (see
    [writev_outcome_is_write_outcome] below).  (The all-readable
    premise [gather_iovecs = Some bs] makes the gatherable prefix the
    whole flattening, so the EFAULT gate is off; a partially readable
    sequence instead delivers prefixes of its [gather_prefix],
    mirroring [write_spec].)  Being handed an [Ok] also pins the
    gathered total inside [rw_bytes_max]: past it the spec is
    [unmodeled], never [Ok].

    That premise reads the CAPPED vector [cap_iovecs iovs], the same
    vector the transfer runs over: an aggregate above [MAX_RW_COUNT]
    writes only the first [MAX_RW_COUNT] bytes, so it is the capped
    flattening — not the imported one — that the return and the events
    follow.  Below the cap the two coincide.

    The import premise is [copy_iovecs_aux ... = ImpOk iovs], not merely
    that the descriptor array is readable: an [iov_len] that is negative
    as [ssize_t] imports as [ImpInval] and the call is -EINVAL, so
    readability alone would not pin the outcome. *)

(** A byte map answering for exactly the bytes of [bs] laid out from
    [base] upward, and [None] everywhere else.  The lower bound is not
    decoration: without it every address below [base] subtracts to a
    negative [Z], which [Z.to_nat] takes to 0, so the map would answer
    the FIRST byte of [bs] for the whole address space below it. *)
Definition bytes_at (base : word) (bs : list byte) : word -> option byte :=
  fun a => if (bv_unsigned base <=? bv_unsigned a)%Z
           then nth_error bs (Z.to_nat (bv_unsigned a - bv_unsigned base))
           else None.

Definition mem_ab : word -> option byte :=
  fun a => if bv_eqb a 4096 then Some 97 else if bv_eqb a 4097 then Some 98 else None.

(** One write("ab")... *)

Definition cap_boundary_iovecs : list (word * word) :=
  [(4096, Z_to_bv 64 (MAX_RW_COUNT - 16));
   (8192, Z_to_bv 64 100);
   (12288, Z_to_bv 64 50)].

Example cap_iovecs_truncates_in_place_and_keeps_the_tail :
  cap_iovecs cap_boundary_iovecs
  = [(4096, Z_to_bv 64 (MAX_RW_COUNT - 16));
     (8192, Z_to_bv 64 16);
     (12288, Z_to_bv 64 0)]
  /\ (iovs_total (cap_iovecs cap_boundary_iovecs) = MAX_RW_COUNT)%Z.
Proof. split; check_eq. Qed.

(** For readv: an iovec array at 8192 whose FIRST descriptor is well
    formed ({4096, 1}) and whose SECOND is UNREADABLE, the array stopping
    at 8208.  That makes the count the model actually used visible in the
    verdict: one descriptor is fine, two is -EFAULT. *)

Example unmodeled_syscall_is_error :
  check_syscall (mkInput 166 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** A read on a nonexistent fd fails with -EBADF — a modeled kernel
    failure, NOT a model error — and is not allowed to SUCCEED. *)

Definition one_map_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 demo_limit)
              (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)).

(** An unaligned addr or len = 0 is -EINVAL, as on Linux. *)

Definition near_ceiling_sum_model : Model :=
  with_vmmaps
    (mkVmMaps [] [(Z_to_bv 64 (two_pow_64 - 8192), 4096)] 0 0 demo_limit)
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)).

(** Reason 3.  A live mapping at [addr + n = 2^64 - 4096], one page
    short of the word's end: [munmap_near_max_is_einval] shows the
    [TASK_SIZE] gate answers -EINVAL there before the exact-match arm
    can see it.  No real
    run ever places a live mapping this close to [2^64] (every range
    Linux hands back sits far below [State.alloc_top]), so only a
    hand-built model can exercise the gate at its own boundary. *)

Definition noaccess_base : Model := init_model [] 0 0 demo_sp 16384 (demo_input [] IEof).

Definition noaccess_three_pages : Model :=
  with_vmmaps
    (mkVmMapsFull [] [(65536, 12288)] [(65536, 12288)] 0 0 16384 0 demo_sp)
    noaccess_base.

(** Reason 3.  A fresh PROT_NONE grant lands in BOTH ledgers: [vm_maps]
    owns and budgets it, [vm_noaccess] records that its overlay is absent.
    A user program sees only the consequences; only this states the pair
    of ledgers the grant produces. *)

Definition stale_overlay (a : word) : option byte :=
  if bv_eqb a 65536 then Some 42 else None.

Definition noaccess_unowned : Model :=
  with_vmmaps (mkVmMapsFull [] [] [(65536, 4096)] 0 0 16384 0 demo_sp) noaccess_base.

Definition noaccess_image_overlap : Model :=
  with_vmmaps (mkVmMapsFull [(4096, 4096)] [(4096, 4096)] [] 0 0 16384 0 demo_sp)
              (init_model [(4096, 4096)] 0 0 demo_sp 16384 (demo_input [] IEof)).

Definition tight_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 8192)
              (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof)).

Definition ceiling_room_model : Model :=
  with_vmmaps (mkVmMaps [] [] 0 0 demo_limit) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)).

Definition region_live_model : Model :=
  with_vmmaps (mkVmMaps [] [(131072, 4096)] 0 0 demo_limit)
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)).

(** [region_free], independent of the ceiling and the budget (both
    generous here: [demo_limit], and the sole live map is 4096 bytes
    against a [demo_limit] budget).  A grant immediately ADJACENT to the
    live mapping [131072, 135168) — [135168, 139264) — is disjoint and
    grants. *)

Example fd_truncation_high_low_halves_all_ebadf :
  Forall (fun fd =>
    check_syscall (mkInput 64 [fd; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
      (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
    = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [])
    [Z_to_bv 64 (2 ^ 31); Z_to_bv 64 (2 ^ 32 - 1); Z_to_bv 64 (2 ^ 64 - 1);
     Z_to_bv 64 (2 ^ 63 + 2 ^ 32 - 1)].
Proof. repeat constructor; check_eq. Qed.

(** ...while a LIVE low half is reached however enormous the register:
    fd = 2^63 is stdin, so a write to it is -EBADF for the RIGHT reason
    (stdin is read-only, [FdChannel 0]) and a read from it is a stdin
    read — at end of input, 0.  Channel direction is an assumption
    about the environment rather than a property of the fd number. *)

Example fd_truncation_live_low_half_under_bit63 :
  check_syscall (mkInput 64 [Z_to_bv 64 (2 ^ 63); 4096; 2; 0; 0; 0]
                   mem_ab (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 63 [Z_to_bv 64 (2 ^ 63); 4096; 16; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [].
Proof. split; check_eq. Qed.

(** The value that comparison runs against — pinned as a numeral, so a
    switch of [fd32] to SIGN-extension (which would make [AT_FDCWD32] the
    full-width -100 again) cannot pass unnoticed.  No trace can present a
    model constant, so nothing but this example pins it. *)

Example at_fdcwd32_is_the_low_half_of_minus_100 :
  AT_FDCWD32 = Z_to_bv 64 4294967196.
Proof. check_eq. Qed.

(** Truncation does not widen AT_FDCWD to "any dirfd whose low half looks
    plausible": a LIVE fd as dirfd is still an unmodeled
    relative-to-a-dirfd open, and still fails closed. *)

Definition wpast_model : Model :=
  mkModel [(3, FdFileW [102] 4)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [104; 105])] None None None.

(** write(3, buf, 0) at that offset transfers nothing and leaves both the
    file and the fd offset alone, as on Linux.  [Fs.file_write] does not
    zero-extend the file out to the offset here. *)

Definition rlim_bytes (soft hard : byte) : list byte :=
  [soft; 0; 0; 0; 0; 0; 0; 0; hard; 0; 0; 0; 0; 0; 0; 0].

(** A writable 16-byte landing zone at 4096 for the read's out-parameter. *)

Definition rlim_out : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4112 then Some 0 else None.

(** A readable source struct at 8192, for the set arm. *)

Definition rlim_src_at (soft hard : byte) : word -> option byte :=
  fun a => if bv_ltu a 8192 then None
           else if bv_eqb a 8192 then Some soft
           else if bv_ltu a 8200 then Some 0
           else if bv_eqb a 8200 then Some hard
           else if bv_ltu a 8208 then Some 0
           else None.

Definition rlim_model : Model := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

(** A NONZERO soft limit on purpose: it is what lets the set below
    actually change the record, so [prlimit64_read_after_set] cannot pass
    by accident. *)

Definition rlim_pinned : Model := with_rlimit_core (rlim_bytes 3 7) rlim_model.

(* ---- uname (160) -------------------------------------------------------- *)

(** A 390-byte writable landing zone at 4096 for [uname]'s only
    out-parameter.  Deliberately EXACT: [uts_out_short] below is the same
    zone one byte shy, which is the shape that separates the -EFAULT arm
    from the decline. *)

Definition uts_out : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4486 then Some 0 else None.

Definition uts_out_short : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4485 then Some 0 else None.

(** Six members, assembled the way the kernel's struct is laid out. *)

Definition uts_name_of (nodename release version domainname : list Z)
    : list byte :=
  uts_literal uts_sysname_chars
  ++ uts_literal nodename
  ++ uts_literal release
  ++ uts_literal version
  ++ uts_literal uts_machine_chars
  ++ uts_literal domainname.

(** "6.18.46" and "6.1.0" — two RELEASE strings, both inside the
    envelope.  Which one a machine reports is not something the kernel
    source settles, so neither is privileged; what the examples below use
    them for is that a run may report one of them and then must go on
    reporting THAT one. *)

Definition uts_release_a : list Z := [54; 46; 49; 56; 46; 52; 54]%Z.
Definition uts_release_b : list Z := [54; 46; 49; 46; 48]%Z.

Definition uts_demo   : list byte := uts_name_of [] uts_release_a [] [].
Definition uts_demo_b : list byte := uts_name_of [] uts_release_b [] [].

(** A name Linux cannot hold: [sysname] reading "Linuy".  Nothing writes
    that member after [init_uts_ns], so the literal is the only value it
    takes. *)

Definition uts_bad_sysname : list byte :=
  uts_literal [76; 105; 110; 117; 121]%Z
  ++ uts_literal [] ++ uts_literal uts_release_a ++ uts_literal []
  ++ uts_literal uts_machine_chars ++ uts_literal [].

(** A [release] with no terminator inside its 65 bytes — every byte
    'A'.  [Kernel.Sys.utsname_wf] leaves the release's CONTENT free and
    still refuses this, which is what makes the terminator conjunct
    separately testable. *)

Definition uts_unterminated_release : list byte :=
  uts_literal uts_sysname_chars ++ uts_literal []
  ++ repeat (Z_to_bv 8 65) 65
  ++ uts_literal [] ++ uts_literal uts_machine_chars ++ uts_literal [].

Definition uts_model : Model := rlim_model.
Definition uts_pinned : Model := with_utsname uts_demo uts_model.

(** The last four bytes of the address space, so the 390-byte copy-out
    covers them and then 386 more at 0 — the shape
    [State.read_bytes_map]'s wrapping walk accepts and
    [State.access_okb]'s [Z] subtraction refuses.  Same construction as
    [Checks.Cases.Fs.Pipe]'s [pipe2_wrap_fildes] and
    [Checks.Cases.Net.Socket]'s socketpair group. *)

Definition uts_wrap_name : word := Z_to_bv 64 (2 ^ 64 - 4).

Definition uts_wrap_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 386)%Z || (2 ^ 64 - 4 <=? bv_unsigned a)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

(** The FIRST read is where the environment's inherited limit enters the
    model: any well-formed pair is admissible, and it becomes the pin. *)

Example argc_zero_invalid : ~ valid_argv [].
Proof. intros [Hlen _]. cbn in Hlen. lia. Qed.

Example argv_single_empty_string_valid : valid_argv [[]].
Proof.
  repeat apply conj.
  - cbn. lia.
  - cbn. lia.
  - change (total_arg_bytes [[]]) with 1%Z. lia.
  - apply Forall_cons; [cbn; lia | apply Forall_nil].
  - apply Forall_cons; [tauto | apply Forall_nil].
  (* the fifth clause is on the TAIL, and this argv has none *)
  - apply Forall_nil.
Qed.

(* ---- the concrete block these checks read -------------------------- *)

(** The fixture layout, spelled once: argv = ["x"], envp = [], the exec
    file name [State.default_execfn], the stack VMA's end at
    [State.sp_window_hi] (riscv64's STACK_TOP, the launch with no stack
    draw) and [sp] at the top of what [create_elf_tables]
    (fs/binfmt_elf.c, Linux v6.18.46, commit 1f99e9ab748f) leaves: the
    whole block is 528 bytes.

    THE BLOCK IS THE WHOLE IMAGE.  [setup_arg_pages] (fs/exec.c)
    page-aligns the top and [create_init_stack_vma] (mm/vma_exec.c)
    leaves only the eight bytes at the very top unwritten, which the
    block itself carries, so there is nothing above [sp + 528] for an
    entry to choose.

    This is a placement a Linux launch really gives — the one
    [Run.launch_entry_va] witnesses — rather than a round number, and
    that is also why it is short: a fixture whose [sp] sat at
    [State.sp_window_lo] with a top near STACK_TOP would make every
    [vm_compute] below walk two gigabytes of pad.

    WHAT WIDENING THIS FIXTURE COSTS, measured, because the next
    person to widen it needs the number: a 4096-byte block did not
    finish one [vm_compute] below in thirty minutes, and these 528
    bytes finish in seconds.  Part of that was [State.init_model]
    being a chain of [with_*] setters — each rebuilds the record from
    its argument's fields, so the chain denotes a term holding the
    PRODUCT of the setters' own copy counts, NOT a power of seven:
    25,071,039 copies of the innermost model over the seven links of
    [State.init_model_setter_chain], against the 823,543 that [7^7]
    would give.  That count and the timings behind it are at
    [State.init_model], measured rather than restated here, and a
    fixture that writes the term twice costs time exponential in the
    chain's length.  [init_model] is one constructor since — a factor
    of 9,935 on this file's own
    [fd_truncation_high_low_halves_all_ebadf] — which is what makes 528
    bytes cheap; the four-kilobyte block was not measured again after
    that. *)

Definition demo_block_top : word := Z_to_bv 64 sp_window_hi.
Definition demo_block_sp : word := Z_to_bv 64 0x7ffffffffdf0.

Definition block_draw : EntryDraw :=
  mkDraw demo_random demo_block_top vdso_keeps_all.
Definition block_draw_zero : EntryDraw :=
  mkDraw (Z_to_bv 128 0) demo_block_top vdso_keeps_all.

Definition demo_block : list byte :=
  entry_stack_image demo_x_input demo_mbase demo_phdrs
    (Z_to_bv 64 (Z.of_N demo_pc)) demo_block_sp block_draw.

Definition demo_block_zero : list byte :=
  entry_stack_image demo_x_input demo_mbase demo_phdrs
    (Z_to_bv 64 (Z.of_N demo_pc)) demo_block_sp block_draw_zero.

Definition demo_mem (draw : EntryDraw) : word -> option byte :=
  ms_mem (init_machine_state [] demo_pc demo_phdrs demo_block_sp demo_mbase
            draw demo_x_input).

(** The vector this layout publishes is the 28-entry one: the kernel
    build [State.default_kernel] has CONFIG_RSEQ, so [create_elf_tables]
    (fs/binfmt_elf.c) emits AT_RSEQ_FEATURE_SIZE and AT_RSEQ_ALIGN, and
    the launch publishes no AT_SYSINFO_EHDR, which is why it is 28 and
    not Linux's 29 ([StackLayout.LaunchAuxv]).  The offsets every check
    below counts with come from that number. *)

Example demo_auxv_has_the_rseq_pair :
  (la_rseq demo_la, auxv_count (la_rseq demo_la), auxv_size (la_rseq demo_la))
  = (true, 28%nat, 448%nat).
Proof. check_eq. Qed.

(** The block runs from [sp] to [StackLayout.ed_top]: its length is the
    distance between them, and the pad [arch_align_stack]
    (arch/riscv/kernel/process.c) left is whatever is over once the
    head, the strings and the skipped slot are taken out — 0 to 4095
    bytes, and 20 here: this fixture is the launch with the smallest
    pad for the OLD head, and the head lost the 16 bytes of the
    AT_SYSINFO_EHDR entry, which the pad took up.  A model that laid a
    shorter block and drew the bytes above it, as this one used to,
    fails the first of these. *)

Example the_block_runs_from_sp_to_the_stack_top :
  Z.of_nat (length demo_block)
  = (entry_page_top block_draw - bv_unsigned demo_block_sp)%Z.
Proof. check_eq. Qed.

Example the_block_measurements_are_linuxs :
  (block_head_size (la_rseq demo_la) demo_argv [],
   launch_string_bytes demo_argv [] default_execfn,
   block_pad_len (la_rseq demo_la) demo_block_sp demo_block_top demo_argv []
     default_execfn,
   length demo_block)
  = (496%nat, 4%nat, 20%nat, 528%nat).
Proof. check_eq. Qed.

(** …and the model maps exactly that range.  The last byte of the block
    is mapped; the byte AT the stack VMA's end is not, because the
    kernel's VMA ends there too.  Under the old layout the bytes above
    the block were a draw of the entry's; there are none now. *)

Example the_image_stops_at_the_stack_top :
  (demo_mem block_draw (Z_to_bv 64 (entry_page_top block_draw - 1)),
   demo_mem block_draw (Z_to_bv 64 (entry_page_top block_draw)))
  = (Some (Z_to_bv 8 0), None).
Proof. check_eq. Qed.

(** The auxv's AT_RANDOM entry carries [at_random_ptr], and the 16 bytes
    there are materialized in the initial stack image (a libc seeding its
    stack canary from AT_RANDOM dereferences the pointer).  What is
    materialized is THIS RUN'S DRAW, the [ed_random] half of
    [Run.ExecEntry]'s [en_draw], laid
    down little-endian; the expected list is written out as literal
    bytes rather than as [at_random_bytes demo_random], so that the check
    pins the serialization and the placement together instead of
    restating the definition. *)

Example at_random_points_at_the_16_drawn_bytes :
  let mem := stack_to_mem demo_block_sp demo_block in
  map (fun k => mem (at_random_ptr demo_block_sp (la_rseq demo_la) demo_argv []
                     + nat_to_word k))
      (seq 0 16)
  = map (fun b => Some (Z_to_bv 8 b))
        [0xf0; 0xe1; 0xd2; 0xc3; 0xb4; 0xa5; 0x96; 0x87;
         0x78; 0x69; 0x5a; 0x4b; 0x3c; 0x2d; 0x1e; 0x0f]%Z.
Proof. check_eq. Qed.

(** The same read at the ZERO draw returns zeros.  Keeping both halves is the point
    of the pair: the check above alone would still pass if the block were
    some other fixed constant, and this one alone would still pass if the
    block were fixed at zero. *)

Example at_random_points_at_zeros_at_the_zero_draw :
  let mem := stack_to_mem demo_block_sp demo_block_zero in
  map (fun k => mem (at_random_ptr demo_block_sp (la_rseq demo_la) demo_argv []
                     + nat_to_word k))
      (seq 0 16)
  = repeat (Some (Z_to_bv 8 0)) 16.
Proof. check_eq. Qed.

(** The draw moves those 16 bytes and NOTHING ELSE: at two draws the
    images agree outside them.  The sixteen bytes are no longer the
    block's tail — Linux puts the strings above them — so the split is
    read with [StackLayout.block_below_random], which is what
    [StackLayout.build_stack_bytes_split_random] says for every
    argument; here it is on a concrete layout, where the two outer
    pieces are a computation rather than a unification side
    condition. *)

Example at_random_block_is_all_the_draw_moves :
  let n := length (block_below_random demo_la demo_phdrs
                     (Z_to_bv 64 (Z.of_N demo_pc)) demo_block_sp demo_block_top
                     demo_argv [] default_execfn demo_uid demo_gid
                     demo_hwcap) in
  (firstn n demo_block, firstn 16 (skipn n demo_block),
   skipn (n + 16) demo_block)
  = (firstn n demo_block_zero, at_random_bytes demo_random,
     skipn (n + 16) demo_block_zero).
Proof. check_eq. Qed.

(** The NEGATIVE half: a proof may NOT assume the block is zero.  If
    [at_random_bytes] were [repeat (Z_to_bv 8 0) 16], this statement
    would be a theorem and every equivalence proof could compute through
    it.  A binary that echoes its AT_RANDOM bytes would then be modeled
    as echoing zeros, so it could be proved equivalent to one that
    really does write sixteen zeros, which is false on almost every real
    run.  The statement is refutable, by the draw the kernel is equally
    free to make. *)

Example zero_at_random_block_is_refuted :
  ~ (forall draw : EntryDraw,
       let mem := stack_to_mem demo_block_sp
                    (entry_stack_image demo_x_input demo_mbase demo_phdrs
                       (Z_to_bv 64 (Z.of_N demo_pc)) demo_block_sp draw) in
       map (fun k => mem (at_random_ptr demo_block_sp (la_rseq demo_la) demo_argv []
                          + nat_to_word k))
           (seq 0 16)
       = repeat (Some (Z_to_bv 8 0)) 16).
Proof.
  intro H. specialize (H block_draw).
  apply (f_equal (map (option_map bv_unsigned))) in H.
  vm_compute in H. discriminate.
Qed.

(** The pointer really is what the auxv slot stores: reading the value
    half of the AT_RANDOM entry back out of the image yields
    [at_random_ptr].  AT_RANDOM is the twenty-fourth of the
    twenty-eight entries this launch writes (index 23, counting
    [ARCH_DLINFO]'s nine first — Linux's ten less AT_SYSINFO_EHDR), so
    its value word starts [16 * 23 + 8] bytes into the vector. *)

Example at_random_auxv_slot_stores_the_pointer :
  let auxv_start := (8 + (1 + 1) * 8 + (0 + 1) * 8)%nat in
  firstn 8 (skipn (auxv_start + 16 * 23 + 8)%nat demo_block)
  = word_le8 (at_random_ptr demo_block_sp (la_rseq demo_la) demo_argv []).
Proof. check_eq. Qed.

(** AT_EXECFN points at the exec file name, which [do_execveat_common]
    (fs/exec.c) copied FIRST and therefore placed at the TOP of the
    string area, right below the eight bytes [create_init_stack_vma]
    skipped.  The name and its NUL are read back out at that address,
    and the address is ten bytes below the stack VMA's end: eight for
    the skipped slot, one for the NUL and one for the name. *)

Example at_execfn_points_at_the_exec_file_name :
  let mem := stack_to_mem demo_block_sp demo_block in
  let p := at_execfn_ptr demo_block_top default_execfn in
  (map (fun k => mem (p + nat_to_word k)) (seq 0 2),
   (bv_unsigned demo_block_top - bv_unsigned p)%Z)
  = ([Some (Z_to_bv 8 97); Some (Z_to_bv 8 0)], 10%Z).
Proof. check_eq. Qed.

(** THREAD-LOCAL STORAGE hinges on this: a static libc finds PT_TLS only
    by walking the program header table, and finds the table only through
    AT_PHDR/AT_PHENT/AT_PHNUM.  They are entries 12, 13 and 14 of the
    vector — [ARCH_DLINFO]'s nine come first, then AT_HWCAP, AT_PAGESZ
    and AT_CLKTCK — so their (type, value) words are words 24..29 of
    the auxv, which starts right after argc, the argv pointers (+ NULL)
    and the envp pointers (+ NULL).  Read them straight back out of the
    initial stack image and check they carry the IMAGE's numbers, not
    zeros. *)

Example auxv_publishes_the_program_header_table :
  let auxv_start := (8 + (1 + 1) * 8 + (0 + 1) * 8)%nat in
  map (fun k => firstn 8 (skipn (auxv_start + 8 * k)%nat demo_block)) (seq 24 6)
  = [ word_le8 AT_PHDR;  word_le8 (Z_to_bv 64 0x10040);
      word_le8 AT_PHENT; word_le8 (Z_to_bv 64 56);
      word_le8 AT_PHNUM; word_le8 (Z_to_bv 64 6) ].
Proof. check_eq. Qed.

(** AT_UID / AT_EUID carry THE RUN'S OWN USER, and the same one the
    credential readers answer.  Linux ties those two together by reading
    one field twice: [create_elf_tables] (fs/binfmt_elf.c) emits
    [NEW_AUX_ENT(AT_UID, from_kuid_munged(cred->user_ns, cred->uid))]
    off [cred = current_cred()], and [SYSCALL_DEFINE0(getuid)]
    (kernel/sys.c) returns [from_kuid_munged(current_user_ns(),
    current_uid())], where [current_uid()] IS [current_cred()->uid] —
    both texts read off Linux v6.18.46 (commit 1f99e9ab748f) and
    byte-identical there and at every mainline release tag from v4.4
    through v6.18.  So a program that reads AT_UID off its own initial
    stack and compares it with [getuid()] always sees them agree, and a
    model that let them differ would
    describe a process no kernel produces.

    NO SYSCALL CHECK REACHES THIS.  The syscall checker folds over the
    syscalls of a run; it never builds the model's initial stack, so
    the auxv side is invisible to it.  The three checks below are the
    evidence instead.

    Read back out of the built image, the way the program header entries
    are above: AT_UID, AT_EUID, AT_GID and AT_EGID are entries 18 to 21,
    so their (type, value) words are words 36..43 of the vector. *)

Example auxv_publishes_the_launching_uid :
  let auxv_start := (8 + (1 + 1) * 8 + (0 + 1) * 8)%nat in
  map (fun k => firstn 8 (skipn (auxv_start + 8 * k)%nat demo_block)) (seq 36 8)
  = [ word_le8 AT_UID;  word_le8 demo_uid;
      word_le8 AT_EUID; word_le8 demo_uid;
      word_le8 AT_GID;  word_le8 demo_gid;
      word_le8 AT_EGID; word_le8 demo_gid ].
Proof. check_eq. Qed.

(** …for EVERY launch, not just [demo_uid]: the four id entries are
    exactly the launching user and group, and there is no fifth entry
    an id could hide in.  Universally quantified, so no finite set of
    traces could establish it.  [la] is destructured because the
    vector's last two entries are there only under CONFIG_RSEQ, and the
    claim holds either way. *)

Lemma auxv_ids_are_exactly_the_launching_ids :
  forall la ph entry uid gid hw ar ae,
  filter (fun e => orb (orb (bv_eqb (fst e) AT_UID) (bv_eqb (fst e) AT_EUID))
                       (orb (bv_eqb (fst e) AT_GID) (bv_eqb (fst e) AT_EGID)))
         (auxv_entries la ph entry uid gid hw ar ae)
  = [(AT_UID, uid); (AT_EUID, uid); (AT_GID, gid); (AT_EGID, gid)].
Proof. intros [c msz [|]] ph entry uid gid hw ar ae; reflexivity. Qed.

(** …and those ids are the ones the READERS answer, not a second copy
    that could drift from them: all four entries hold the credentials
    [State.init_model] builds, which is what [Kernel.Sys.getid_spec]
    projects.  This is the whole argument — one source, so the two
    cannot disagree. *)

Lemma auxv_ids_are_the_credentials_the_readers_answer :
  forall reserved brk0 mbase sp lim inp la ph entry ar ae,
    let m := init_model reserved brk0 mbase sp lim inp in
    filter (fun e => orb (orb (bv_eqb (fst e) AT_UID) (bv_eqb (fst e) AT_EUID))
                         (orb (bv_eqb (fst e) AT_GID) (bv_eqb (fst e) AT_EGID)))
           (auxv_entries la ph entry (in_uid inp) (in_gid inp) (in_hwcap inp)
              ar ae)
    = [ (AT_UID,  cr_uid  (m_creds m)); (AT_EUID, cr_euid (m_creds m));
        (AT_GID,  cr_gid  (m_creds m)); (AT_EGID, cr_egid (m_creds m)) ].
Proof.
  intros reserved brk0 mbase sp lim inp [c msz [|]] ph entry ar ae;
    reflexivity.
Qed.

(** ** AT_HWCAP: the entry, its range, and what the range excludes

    AT_HWCAP is the one auxv value that is neither the image's nor the
    launching user's: it describes the HART.  [Run.valid_hwcap] admits
    two words and no more, and the checks below are what say that the
    pair is a pair — that both members are really admitted, that the
    entry really carries the launch's word, and that the model refuses
    the masks a kernel would not publish.  The kernel argument for
    exactly these two is in [StackLayout]'s AT_HWCAP bullet.

    NO SYSCALL CHECK REACHES THESE, for the same reason the id checks
    above are unreachable: the syscall checker never builds the model's
    initial stack.

    First the entry is THERE, and where Linux puts it: AT_HWCAP is the
    first entry [create_elf_tables] writes after [ARCH_DLINFO], which
    this model publishes as NINE entries rather than Linux's ten (no
    AT_SYSINFO_EHDR — [StackLayout.LaunchAuxv]), immediately before
    AT_PAGESZ.  So it is entry 9 here, entry 10 on Linux, and its
    (type, value) words are words 18 and 19 of this vector. *)

Example auxv_publishes_the_hart_capabilities :
  let auxv_start := (8 + (1 + 1) * 8 + (0 + 1) * 8)%nat in
  map (fun k => firstn 8 (skipn (auxv_start + 8 * k)%nat demo_block)) (seq 18 4)
  = [ word_le8 AT_HWCAP;  word_le8 demo_hwcap;
      word_le8 AT_PAGESZ; word_le8 (Z_to_bv 64 4096) ].
Proof. check_eq. Qed.

(** …carrying the LAUNCH'S word, for every launch, and there is no
    second entry a hwcap could hide in.  Universally quantified, so no
    finite set of traces could establish it — the same shape as
    [auxv_ids_are_exactly_the_launching_ids] above. *)

Lemma auxv_hwcap_is_exactly_the_launch_word :
  forall la ph entry uid gid hw ar ae,
  filter (fun e => bv_eqb (fst e) AT_HWCAP)
         (auxv_entries la ph entry uid gid hw ar ae)
  = [(AT_HWCAP, hw)].
Proof. intros [c msz [|]] ph entry uid gid hw ar ae; reflexivity. Qed.

(** BOTH masks are admitted.  Without this the disjunction could have
    been written with an unsatisfiable second arm and every proof would
    still go through, which is exactly the "quantifier that says
    nothing" failure [Equivalence.image_brk_satisfiable] guards against
    elsewhere. *)

Lemma valid_hwcap_admits_both_masks :
  valid_hwcap hwcap_rv64gc /\ valid_hwcap hwcap_rv64gcv.
Proof. split; [left | right]; reflexivity. Qed.

(** …and the two are DIFFERENT, so quantifying over them is quantifying
    over something.  Compared on unsigned values, the way
    [the_constant_zero_auxv_is_refuted] below compares vectors. *)

Example the_two_hwcap_masks_are_distinct :
  bv_unsigned hwcap_rv64gc <> bv_unsigned hwcap_rv64gcv.
Proof. vm_compute. discriminate. Qed.

(** …and the difference is exactly the V bit, which is the whole claim:
    the six extensions the decoder implements are present in both, and
    the only word that moves is [COMPAT_HWCAP_ISA_V], [1 << ('V' -
    'A')] (arch/riscv/include/uapi/asm/hwcap.h, Linux v6.18.46, commit
    1f99e9ab748f).  Written as an arithmetic identity rather than as two
    literals so that changing either constant without changing the other
    fails here. *)

Example the_two_masks_differ_in_the_v_bit_alone :
  (bv_unsigned hwcap_rv64gcv - bv_unsigned hwcap_rv64gc)%Z = (2 ^ 21)%Z.
Proof. vm_compute. reflexivity. Qed.

(** THE NEGATIVE, first half: the model refuses the word an ABSENT
    entry effectively delivers.  A runtime that looks the type up and
    finds nothing uses its default, zero — a hart with no extensions at
    all, on which none of this model's instructions could run.  Nothing
    in [valid_hwcap] admits it. *)

Example valid_hwcap_refuses_the_absent_entrys_zero :
  ~ valid_hwcap (Z_to_bv 64 0).
Proof. intros [H | H]; apply (f_equal bv_unsigned) in H; vm_compute in H;
       discriminate. Qed.

(** THE NEGATIVE, second half: it also refuses two words that are
    WRONG IN OPPOSITE DIRECTIONS, which is what makes the pair a range
    rather than a shrug.

    [0x112C] drops the A bit ([COMPAT_HWCAP_ISA_A] is bit 0) from an
    otherwise-RV64GC mask: a hart without atomics, which cannot run the
    [Riscv.Instr] AMOs this semantics interprets, so the model must not
    describe a process on one.  [0x40112D] adds bit 22 — the letter W,
    which the [isa2hwcap] table never assigns
    (arch/riscv/kernel/cpufeature.c, Linux v6.18.46, commit
    1f99e9ab748f: the [unsigned long isa2hwcap[26]] that
    [riscv_fill_hwcap] declares and seeds itself, seven indices set and
    the other nineteen left zero), so no kernel publishes it and
    admitting it would put the model outside what that kernel tree can
    produce.

    The citation names the FUNCTION and the declaration, not a line.  A
    line number rots with the next patch and nothing in this tree
    checks it.  The declaration is named because [riscv_fill_hwcap] is
    not unique as a string in that file: it is also the prefix of
    [riscv_fill_hwcap_from_isa_string] and
    [riscv_fill_hwcap_from_ext_list], which take the table as a
    parameter rather than seeding it, so a reader grepping the bare
    name lands on three functions and the seeding is in only one. *)

Example valid_hwcap_refuses_masks_no_kernel_publishes :
  ~ valid_hwcap (Z_to_bv 64 0x112C) /\ ~ valid_hwcap (Z_to_bv 64 0x40112D).
Proof.
  split; intros [H | H]; apply (f_equal bv_unsigned) in H;
    vm_compute in H; discriminate.
Qed.

(** THE NEGATIVE, third half: the vector WITHOUT AT_HWCAP is not what
    the model builds.  Stated on the entry TYPES, so it is a claim
    about the entry SET rather than about any value: a model that
    dropped the entry, or moved it behind AT_PAGESZ where Linux does
    not put it, fails here. *)

Example the_hwcap_less_auxv_is_refuted :
  map (fun e => bv_unsigned (fst e))
      (auxv_entries demo_la demo_phdrs (Z_to_bv 64 0) demo_uid demo_gid
         demo_hwcap (Z_to_bv 64 0) (Z_to_bv 64 0))
  <> [40; 41; 42; 43; 44; 45; 46; 47; 51;
      6; 17; 3; 4; 5; 7; 8; 9; 11; 12; 13; 14; 23; 25; 31; 27; 28; 0]%Z.
Proof. vm_compute. discriminate. Qed.

(** The entry set the model DOES build, in order, as the positive twin
    of that refutation: [ARCH_DLINFO]'s entries
    (arch/riscv/include/asm/elf.h) first, because fs/binfmt_elf.c
    expands it before its own entries — NINE of them here, Linux's ten
    less the AT_SYSINFO_EHDR this model does not publish
    ([StackLayout.LaunchAuxv]) — then [create_elf_tables]'s sixteen,
    then the CONFIG_RSEQ pair, then AT_NULL. *)

Example the_auxv_entry_types_in_order :
  map (fun e => bv_unsigned (fst e))
      (auxv_entries demo_la demo_phdrs (Z_to_bv 64 0) demo_uid demo_gid
         demo_hwcap (Z_to_bv 64 0) (Z_to_bv 64 0))
  = [40; 41; 42; 43; 44; 45; 46; 47; 51;
     16; 6; 17; 3; 4; 5; 7; 8; 9; 11; 12; 13; 14; 23; 25; 31; 27; 28; 0]%Z.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions auxv_hwcap_is_exactly_the_launch_word.
Print Assumptions valid_hwcap_admits_both_masks.

(** THE NEGATIVE.  A literal [AT_UID = AT_EUID = 0] for every process
    would make the model admit a trace where [getuid()] disagrees with
    the stack the same process was handed.  Construct that auxv and
    check it is refused: a process
    launched as [demo_uid] does NOT get the vector a root launch gets.
    Compared on unsigned values, so the disagreement is a difference
    between two lists of integers rather than between [bv] records
    carrying opaque well-formedness proofs. *)

Example the_constant_zero_auxv_is_refuted :
  map (fun e => bv_unsigned (snd e))
      (auxv_entries demo_la demo_phdrs (Z_to_bv 64 0) demo_uid demo_gid
         demo_hwcap (Z_to_bv 64 0) (Z_to_bv 64 0))
  <> map (fun e => bv_unsigned (snd e))
         (auxv_entries demo_la demo_phdrs (Z_to_bv 64 0) (Z_to_bv 64 0)
            (Z_to_bv 64 0) demo_hwcap (Z_to_bv 64 0) (Z_to_bv 64 0)).
Proof. vm_compute. discriminate. Qed.
