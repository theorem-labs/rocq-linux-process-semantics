(** * LinuxProcessSem.Sys.Mm.Mprotect — mprotect (226)

    This file answers to Linux [mm/mprotect.c]: it holds what the kernel
    defines there, and nothing else.  Which file a spec belongs in is
    therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** mprotect: ENOMEM only, and only on the branch that turns an
    inaccessible range read-write.  Every other failure a real kernel
    could report is either impossible once the argument gates below have
    passed, or outside the modeled syscall surface (Linux v6.18.46,
    mm/mprotect.c [do_mprotect_pkey] / [mprotect_fixup], on riscv64):

    - ENOMEM is genuine: making a range writable can exceed RLIMIT_AS /
      RLIMIT_DATA ([may_expand_vm], mm/mprotect.c:801-803) or the commit
      charge ([security_vm_enough_memory_mm], :807-808), and splitting the
      VMA at the range's edges can fail on the map_count limit or on
      allocation ([vma_modify_flags], mm/vma.c:1682-1705, through
      [vma_modify], :1665 and :1673, calling [split_vma], :587-594, whose
      [__split_vma] allocates at :510-512, :523-524 and :530-532).  None
      of that is tracked, so it stays injectable.

    - EINVAL is UNREACHABLE past the gates.  Every -EINVAL in
      [do_mprotect_pkey] is one of: the PROT_GROWSDOWN|PROT_GROWSUP
      conflict (:876-877), decided by [mprotect_grows_conflict_b] before
      the spec reaches here; the GROWSDOWN/GROWSUP VMA checks (:913-915,
      :921-923), which that gate does NOT cover — [grows] is read at :867
      before [prot] is masked at :875, so a SINGLE grows bit survives to
      them — but which [mprotect_modeled_b] excludes, since it admits only
      [prot] equal to PROT_READ|PROT_WRITE and any grows bit sends the
      call to [unmodeled] instead; the alignment check (:879-880), decided
      first as well; [arch_validate_prot] (:887-888), which on riscv64
      takes the generic definition (include/linux/mman.h:106-110) and
      accepts anything within PROT_READ|PROT_WRITE|PROT_EXEC|PROT_SEM, so
      it accepts the modeled rw; the pkey check (:899-901), dead because
      [SYSCALL_DEFINE3(mprotect)] (mm/mprotect.c:1008-1011) passes
      pkey = -1 and riscv64 selects no ARCH_HAS_PKEYS; and
      [arch_validate_flags] (:971-974), also the generic always-true
      definition on riscv64
      (include/linux/mman.h:119-123, and riscv64 has no
      arch/riscv/include/asm/mman.h to override either hook).
      [mprotect_fixup] returns no -EINVAL at all on an anonymous VMA.
      The vDSO pair is the exception, and so is the -EACCES of the vvar
      range: both are answered in [mprotect_vdso], not through this
      list.

    Two errnos a real kernel CAN still return are deliberately outside the
    modeled surface, rather than silently absorbed:

    - EINTR from [mmap_write_lock_killable] (mm/mprotect.c:892-893) cannot
      be observed by any program.  It comes from [down_write_killable]
      (kernel/locking/rwsem.c:1598-1610), whose wait state is
      TASK_KILLABLE (:1331, :1496), and [signal_pending_state] aborts a
      TASK_KILLABLE wait only on a FATAL signal
      (include/linux/sched/signal.h:408-416: TASK_KILLABLE lacks
      TASK_INTERRUPTIBLE, so the result is [__fatal_signal_pending]).  A
      fatal signal kills the task before it returns to userspace, so the
      -EINTR never reaches a register the program can read.

    - EPERM for an mseal'd VMA ([vma_is_sealed], mm/mprotect.c:766-767,
      defined in mm/vma.h:611-614; v6.12's [can_modify_vma]) is
      unreachable because [mseal] (__NR_mseal, 462) is not in
      [syscall_spec]'s modeled surface, so VM_SEALED is never set on a
      modeled run.

    An LSM may also fail [security_file_mprotect] (mm/mprotect.c:824), but
    the default hook returns 0 (include/linux/lsm_hook_defs.h:198). *)
Definition mprotect_errnos : list Z := [ENOMEM].

(** [mprotect addr len prot].  Linux decides FOUR things about the
    arguments before it ever looks at the address space, and the spec
    follows that order exactly because the order is behavior — a
    zero-length call must answer 0 for a [prot] the model could not
    otherwise interpret, a grows-conflict must answer -EINVAL even for
    a [prot] that is otherwise fine, and a range whose end wraps must
    answer -ENOMEM even for a [prot] that would itself be -EINVAL.  Linux
    v6.12, mm/mprotect.c [do_mprotect_pkey] (:715, :721-736):

      715  const int grows = prot & (PROT_GROWSDOWN|PROT_GROWSUP);
      721  start = untagged_addr(start);
      723  prot &= ~(PROT_GROWSDOWN|PROT_GROWSUP);
      724  if (grows == (PROT_GROWSDOWN|PROT_GROWSUP))
      725      return -EINVAL;
      727  if (start & ~PAGE_MASK) return -EINVAL;
      729  if (!len) return 0;
      731  len = PAGE_ALIGN(len);
      732  end = start + len;
      733  if (end <= start) return -ENOMEM;

    [untagged_addr] is the identity on riscv64 — only arm64 and x86
    override it (include/linux/uaccess.h:25-27,
    arch/arm64/include/asm/memory.h:286,
    arch/x86/include/asm/uaccess_64.h:37) — so the alignment test sees the
    address the program passed.  A zero [len] returns 0 for EVERY [prot]
    that clears the grows conflict, including PROT_EXEC and unknown high
    bits: nothing is mapped, nothing is protected, and the prot word is
    never validated ([arch_validate_prot] is at :735, past the [!len]
    return).  The wrap check at :733 sits in that same window, so a
    wrapping range is -ENOMEM for every [prot] too.

    The supported NONEMPTY operation is exactly PROT_READ|PROT_WRITE over
    one tracked anonymous range.  On an already-rw
    subrange it is a no-op; on one contained [vm_noaccess] interval it removes
    that interval (splitting when necessary) and exposes fresh zeroes through
    [eff_zeros], provided the resulting backing fits [vm_limit].  Ordinary
    mappings charge at the permission transition; MAP_NORESERVE mappings keep
    their lazy provenance and charge on first data access.  That split is
    Linux's: [mprotect_fixup] (mm/mprotect.c, Linux v6.12) takes the commit
    charge when a private mapping turns writable, but guards it with
    [if (!(oldflags & VM_NORESERVE))], so a range mapped MAP_NORESERVE is
    never charged at the transition.  Unmapped,
    mixed-protection, image, and spanning ranges fail
    closed.  Every other [prot] is unmodeled at nonzero length:

    - PROT_EXEC (bit 2) would make a data page executable.  The model cannot
      fetch from it AT ALL, so answering 0 and letting the source jump
      into the page reports a [MachineFault] for a program that runs
      fine on Linux — [Run.all_traces_error] holds, [Equivalence.equiv]'s
      escape fires, and any target is accepted.  Declining instead makes
      the call [Run.unmodeled_at], which [Equivalence.modeled] rejects.
    - mprotect to PROT_NONE, or dropping 'w'/'r', would require preserving
      arbitrary old contents behind a permission transition.  The bounded
      ledger intentionally supports only zero-backed pages created as
      PROT_NONE by anonymous mmap/MAP_FIXED.

      PROT_READ ALONE is the shape a real allocator reaches for — fill a
      buffer, then downgrade it — so it is worth saying what stops it
      here rather than leaving the reader to conclude the gap is an
      oversight.  Linux takes it on the ordinary path — mm/mprotect.c
      [do_mprotect_pkey] / [mprotect_fixup] compute newflags from prot
      and clear VM_WRITE — so the mapping stays live and readable with
      its contents intact.  What the MODEL lacks is anywhere to
      put such a page.  Anonymous memory has exactly one representation,
      [RiscvSemantics.machine_state]'s writable overlay [ms_mem], and that
      one map answers two different questions: it is the only source of
      readable anonymous bytes ([RiscvSemantics.ov_read_bytes] falls back
      to the loaded segments, never to [ms_rom]), and it is the whole of
      the writable view ([RiscvSemantics.wview], hence
      [RiscvSemantics.store_ok] and the [State.in_wmem] gate every spec
      checks an output buffer against).  So a page that is readable and
      not writable has no encoding: leave the bytes in [ms_mem] and the
      model admits a store Linux answers with SIGSEGV and a syscall
      output buffer Linux answers with -EFAULT; take them out and a load
      Linux serves faults instead — the direction the PROT_EXEC note
      above rejects, since [Run.all_traces_error] then frees the target.
      Modelling it is therefore not a new arm but a new dimension: a
      channel from a [State.SyscallEffect] to the read-only view (nothing
      else reaches [Run.apply_effect]), an [ms_rom] fallback in
      [RiscvSemantics.ov_read_bytes] so a downgraded page still loads,
      and a ledger beside [State.vm_noaccess] so [munmap], [mremap],
      [brk] and the already-rw branch below decline over a downgraded
      range instead of silently re-exposing it.

    A range that is NOT fully contained in the tracked mappings is
    [unmodeled] rather than the -ENOMEM Linux returns for a start outside
    every VMA (mm/mprotect.c [do_mprotect_pkey]), and that is deliberate:
    the ledger is not a complete picture of the address space, so "absent
    from [vm_maps]" does not entail "absent from every VMA".  The stack is
    the standing counterexample — it carries no entry at all, by the
    argument at [State.alloc_top] — so answering that errno would be a
    guess wherever the model's picture is thinner than Linux's.

    NO 32-bit truncation here, deliberately, and it is not an oversight
    of the kind [Syscall.fd32] fixes: the kernel's own prototype is
    [SYSCALL_DEFINE3(mprotect, unsigned long, start, size_t, len,
    unsigned long, prot)], so [prot] is a full register, and
    [arch_validate_prot] rejects any bit outside
    PROT_READ|PROT_WRITE|PROT_EXEC|PROT_SEM with -EINVAL
    (mm/mprotect.c:735-736, include/linux/mman.h:108-111).  A [prot] with
    garbage in its high half is therefore a real -EINVAL on Linux at
    nonzero length, and comparing the whole 64-bit word makes it
    unmodeled here — fail closed, which is the safe direction (answering
    0 would have the model admit a success no kernel produces).  At zero
    length the same garbage is a real 0, which is why the [!len] branch
    below does not consult [prot] at all. *)

(** The one [prot] the model can answer for at nonzero length: exactly
    the rw permissions its anonymous memory already has. *)
Definition mprotect_modeled_b (prot : word) : bool :=
  Z.eqb (bv_unsigned prot) (PROT_READ + PROT_WRITE).

(** Both stack-extension modifiers at once — the ONE argument error the
    modeled surface takes from [prot]'s grows bits (mm/mprotect.c:715,
    :724-725, "can't be both").  Either one alone is legal, and both are
    masked out of [prot] (:723) either way; only the pair is -EINVAL, and
    a lone bit goes on to gate the vma checks at :757 and :767. *)
Definition mprotect_grows_conflict_b (prot : word) : bool :=
  negb (Z.eqb (Z.land (bv_unsigned prot) PROT_GROWSDOWN) 0)
  && negb (Z.eqb (Z.land (bv_unsigned prot) PROT_GROWSUP) 0).

(** Expose one protected range while carrying MAP_NORESERVE provenance and
    already-materialized pages across unchanged.  The post-state budget test
    therefore charges an ordinary mapping now, but leaves a lazy mapping to
    first-touch accounting. *)
Definition mprotect_model_next (m : Model) (addr n : word) : Model :=
  let h := m_vmmaps m in
  with_vmmaps
    (mkVmMapsFull (vm_reserved h) (vm_maps h)
      (maps_subtract (vm_noaccess h)
         (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
      (vm_start_brk h) (vm_brk h) (vm_limit h)
      (vm_mmap_base h) (vm_init_sp h)) m.

(** The protected list only SHRINKS here — exposing a range cuts it out
    — so the ledger goes on naming real bytes.  This is [mprotect]'s
    share of the obligation the section in [Mm/Mmap.v] sets out; see
    [State.entries_nonzero] for why the property is worth having and
    [Madvise.madvise_noaccess_decline_names_a_protected_byte] for who
    reads it. *)
Lemma mprotect_model_next_noaccess_nonzero : forall m addr n,
  vm_noaccess_entries_nonzero (m_vmmaps m) ->
  vm_noaccess_entries_nonzero (m_vmmaps (mprotect_model_next m addr n)).
Proof.
  intros m addr n H.
  unfold vm_noaccess_entries_nonzero, mprotect_model_next in *.
  cbv zeta. rewrite m_vmmaps_with_vmmaps. cbn [vm_noaccess].
  now apply maps_subtract_nonzero.
Qed.

Definition mprotect_budget_ok (m : Model) (addr n : word) : bool :=
  vm_backing_within_limit (mprotect_model_next m addr n).

(** [x] is a mapped byte of the vvar range of the vDSO pair. *)
Definition vdso_vvar_byte (v : VdsoState) (x : Z) : bool :=
  (vds_vvar_mapped v && (vdso_vvar_lo v <=? x)%Z && (x <? vdso_vvar_hi v)%Z)%bool.

(** AN rw mprotect THAT STARTS IN THE vDSO PAIR.  A range that no
    recorded mapping contains reaches here; when its first byte is a
    mapped byte of the pair, [do_mprotect_pkey]'s walk (mm/mprotect.c:
    903-997, Linux v6.18.46) starts at that range of the pair, and the
    answer is Linux's:

    - the VVAR range is VM_READ|VM_MAYREAD without VM_MAYWRITE
      ([vdso_install_vvar_mapping], lib/vdso/datastore.c:99-105), so
      the walk's first test refuses rw with -EACCES (mm/mprotect.c:
      959-963), before anything changes;
    - the TEXT range is VM_MAYWRITE (arch/riscv/kernel/vdso.c:137-140),
      so the walk reaches [mprotect_fixup] (:990).  rw differs from the
      text's flags (:769), the write accounting may refuse with -ENOMEM
      (:799-810), and [vma_modify_flags] (:816) then splits the text
      where the request ends inside it ([vma_modify], mm/vma.c:
      1664-1677): [split_vma]'s map-count -ENOMEM (:590-591) or
      [special_mapping_split]'s -EINVAL (mm/mmap.c:1394-1412).  A
      request that covers the whole text makes it writable, and the
      text's bytes are the kernel's, so that call is [unmodeled].

    A range that meets the pair but starts outside it starts the walk at
    a VMA or hole the ledger may not describe, and stays [unmodeled]. *)
Definition mprotect_vdso (v : VdsoState) (addr : word) (nZ : Z)
    : Sys SyscallEffect :=
  if vdso_vvar_byte v (bv_unsigned addr) then err_ret EACCES
  else if vdso_split v (bv_unsigned addr) (bv_unsigned addr + nZ)
  then alt (e <- errno_from mprotect_errnos ;; err_ret e) (err_ret EINVAL)
  else unmodeled.

Definition mprotect_spec (addr len prot : word) : Sys SyscallEffect :=
  if mprotect_grows_conflict_b prot then err_ret EINVAL
  else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then err_ret EINVAL
  else if w_is0 len then ret_only (Z_to_bv 64 0)
  (* The fourth gate, and it too precedes any reading of [prot]
     (mm/mprotect.c:731-734, before [arch_validate_prot] at :735):

       731  len = PAGE_ALIGN(len);
       732  end = start + len;
       733  if (end <= start) return -ENOMEM;

     [start], [len] and [end] are all 64 bits wide on riscv64
     ([do_mprotect_pkey]'s [unsigned long] / [size_t]), so [end] is the
     WRAPPED sum and [end <= start] is precisely "the sum reached 2^64" —
     which is what this test says in [Z].  The two ways to reach it agree:
     a [len] in the top 4095 values makes C's own [PAGE_ALIGN] wrap to 0,
     leaving [end == start], and [page_round_up_Z] (exact in [Z]) answers
     2^64 there, so [addr + nZ >= 2^64] holds for every [addr].  Below the
     gate [len <> 0] already holds, so [nZ >= 4096] and the sum can never
     be [<= start] any other way.

     This REPLACES a narrower [two_pow_64 <=? nZ] test that fired only
     when the page rounding alone overflowed: [mprotect(2^63, 2^63, rw)]
     rounds to [nZ = 2^63], passed that test, and reached the containment
     gate to be answered [unmodeled] — where Linux wraps [end] to 0 and
     returns -ENOMEM.

     PASSING THIS GATE IS WHAT KEEPS THE ARITHMETIC BELOW HONEST, and the
     old test's real job: [bv_unsigned addr + nZ < 2^64] with
     [bv_unsigned addr >= 0] gives [nZ < 2^64], so [Z_to_bv 64 nZ] cannot
     wrap; and it bounds the SUM as well, so the whole range fits the
     address space and the [(addr, n)] pair below names the range asked
     for.  The narrower test bounded only [nZ] and left that sum free: at
     [addr = 2^63], [nZ = 2^63] the range's end reaches 2^64 exactly, and
     any [word] reconstruction of it lands on 0.  Nothing reachable hit
     that (the containment gate rejects such a range first), but the
     bound is now structural rather than incidental — and the end handed
     to [maps_subtract] is carried in [Z], so no reconstruction happens
     in the first place. *)
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z
  then err_ret ENOMEM
  else if mprotect_modeled_b prot then
    m <- get_model ;;
    let h := m_vmmaps m in
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    (* The [vm_maps] conjunct is what makes this branch sound on its own,
       including during the documented same-page brk-shrink state where a
       physical [vm_noaccess] tail may extend past byte-granular [vm_maps]
       (State.v, purpose (c)).  Linux answers -ENOMEM, not 0, for a range
       that starts outside every VMA (mm/mprotect.c:753, :765-766), so
       without it a ledger violating the invariant would have the model
       return 0 AND zero-fill unmapped memory.

       [vm_noaccess ⊆ vm_maps] is NOT an invariant of reachable states, so
       the conjunct is not implied and it does change the answer: the
       same-page brk-shrink state above is reachable, and an rw [mprotect]
       of that page names a range [vm_noaccess] contains and [vm_maps] does
       not.  [noaccess_vm.c]'s [brk-samepage-protect] mode reaches exactly
       that state and is the only case in the conformance suite that fails
       when the conjunct is dropped.  Nothing in the tree states the
       containment, and nothing should. *)
    if map_contains (vm_noaccess h) addr n && map_contains (vm_maps h) addr n
    then
      alt
        (e <- errno_from mprotect_errnos ;; err_ret e)
        (_ <- choose (fun _ : unit => mprotect_budget_ok m addr n = true) ;;
         modify (fun _ => mprotect_model_next m addr n) ;;
         pure (mkEffect (Z_to_bv 64 0) [] [(addr, n)]))
    (* An already-rw range CANNOT fail: [mprotect_fixup] short-circuits on
       [newflags == oldflags] (mm/mprotect.c:617-620) before [may_expand_vm]
       (:649), the commit charge (:655) and [vma_modify_flags] (:664), so
       there is no split, no map_count check and no accounting to fail.
       The equality holds even for a strict subrange, because [newflags] is
       computed from [prot] and the VMA's own flags rather than from the
       range (:801-805; VM_FLAGS_CLEAR is 0 on riscv64 —
       include/linux/mm.h:486-490, include/linux/pkeys.h:16).  Neither
       -EACCES fires either: [do_mmap] sets VM_MAYREAD|VM_MAYWRITE|VM_MAYEXEC
       unconditionally (mm/mmap.c:347-348) so :807-811 cannot trip, and
       :813-816 needs VM_EXEC in [newflags] (include/linux/mman.h:201-220),
       which rw does not set.  -EAGAIN does not exist on this path. *)
    else if map_contains (vm_maps h) addr n
            && region_free (vm_noaccess h) addr n then
      ret_only (Z_to_bv 64 0)
    else if vdso_byte (m_vdso m) (bv_unsigned addr)
    then mprotect_vdso (m_vdso m) addr nZ
    else unmodeled
  else unmodeled.

(* =========================================================================
   THE BUDGET MARK for mprotect (see [Mmap.brk_budget_refused_b] for
   what a mark is)
   ========================================================================= *)

(** The one charging branch is the exposure of a PROT_NONE range inside
    a live mapping, gated by [mprotect_budget_ok] on the post-state; its
    [choose] is over [unit], so the gate reads nothing but the request
    and the pre-state and the mark is exact.  The four argument gates,
    the already-rw no-op and the unmodeled shapes never fire it. *)
Definition mprotect_budget_refused_b (addr len prot : word) (m : Model) : bool :=
  if mprotect_grows_conflict_b prot then false
  else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then false
  else if w_is0 len then false
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z
  then false
  else if mprotect_modeled_b prot then
    let h := m_vmmaps m in
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    if map_contains (vm_noaccess h) addr n && map_contains (vm_maps h) addr n
    then negb (mprotect_budget_ok m addr n)
    else false
  else false.
