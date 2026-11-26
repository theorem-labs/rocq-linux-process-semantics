(** * LinuxProcessSem.Checks.Cases.Mm.Mprotect — worked examples over mprotect (226)

    Mirrors [Sys/Mm/Mprotect.v], which answers to Linux [mm/mprotect.c]:
    this file holds the worked examples for the syscalls defined there,
    and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude Fs.ReadWrite.

Example mprotect_middle_splits_noaccess_and_zeros_exactly :
  check_syscall
    (mkInput 226 [69632; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(69632, 4096)]) noaccess_three_pages
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(65536, 12288)]
          [(65536, 4096); (73728, 4096)] 0 0 16384 0 demo_sp)
        noaccess_three_pages) [].
Proof. check_eq. Qed.

Example mprotect_noaccess_errno_preserves_ledger :
  check_syscall
    (mkInput 226 [69632; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages
  = CheckOk noaccess_three_pages [].
Proof. check_eq. Qed.

(** Exposing a reserved page consumes backed capacity at the permission
    transition.  With a zero-byte budget the successful effect is rejected,
    while the modeled ENOMEM outcome remains available. *)
Definition noaccess_zero_backing : Model :=
  with_vmmaps
    (mkVmMapsFull [] [(65536, 4096)] [(65536, 4096)] 0 0 0 0 demo_sp)
    noaccess_three_pages.

Example mprotect_over_backed_budget_rejects_success :
  check_syscall
    (mkInput 226 [65536; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(65536, 4096)]) noaccess_zero_backing
  = CheckReject.
Proof. check_eq. Qed.

Example mprotect_over_backed_budget_allows_enomem :
  check_syscall
    (mkInput 226 [65536; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] []) noaccess_zero_backing
  = CheckOk noaccess_zero_backing [].
Proof. check_eq. Qed.

Example mprotect_unmapped_forged_success_is_unmodeled :
  check_syscall
    (mkInput 226 [131072; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) noaccess_three_pages
  = CheckUnmodeled.
Proof. check_eq. Qed.

Example mprotect_already_rw_errno_is_rejected :
  check_syscall
    (mkInput 226 [65536; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = CheckReject.
Proof. check_eq. Qed.

Example mprotect_noaccess_outside_vm_maps_is_unmodeled :
  check_syscall
    (mkInput 226 [65536; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(65536, 4096)]) noaccess_unowned
  = CheckUnmodeled.
Proof. check_eq. Qed.

Example mprotect_wrapping_end_is_enomem :
  check_syscall
    (mkInput 226 [9223372036854775808; 9223372036854775808; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages
  = CheckOk noaccess_three_pages [].
Proof. check_eq. Qed.

Example mprotect_wrapping_end_success_is_rejected :
  check_syscall
    (mkInput 226 [9223372036854775808; 9223372036854775808; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) noaccess_three_pages
  = CheckReject.
Proof. check_eq. Qed.

Example mprotect_wrapping_end_precedes_unsupported_prot :
  check_syscall
    (mkInput 226 [9223372036854775808; 9223372036854775808; 4; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages
  = CheckOk noaccess_three_pages [].
Proof. check_eq. Qed.

Example mprotect_unaligned_precedes_zero_length :
  check_syscall
    (mkInput 226 [65537; 0; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_three_pages
  = CheckOk noaccess_three_pages [].
Proof. check_eq. Qed.

Example mprotect_growsdown_alone_is_not_a_conflict :
  check_syscall
    (mkInput 226 [65536; 0; 16777219; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) noaccess_three_pages
  = CheckOk noaccess_three_pages [].
Proof. check_eq. Qed.

Example mprotect_growsup_alone_is_not_a_conflict :
  check_syscall
    (mkInput 226 [65536; 0; 33554435; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) noaccess_three_pages
  = CheckOk noaccess_three_pages [].
Proof. check_eq. Qed.

Example mprotect_growsdown_alone_einval_is_rejected :
  check_syscall
    (mkInput 226 [65536; 0; 16777219; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_three_pages
  = CheckReject.
Proof. check_eq. Qed.

Example mprotect_growsup_alone_einval_is_rejected :
  check_syscall
    (mkInput 226 [65536; 0; 33554435; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_three_pages
  = CheckReject.
Proof. check_eq. Qed.

Example mprotect_grows_conflict_is_einval :
  check_syscall
    (mkInput 226 [65536; 0; 50331651; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_three_pages
  = CheckOk noaccess_three_pages [].
Proof. check_eq. Qed.

Definition mprotect_lazy_guard : Model :=
  with_vm_backing [(65536, 8192)] [65536]
    (with_vmmaps
      (mkVmMapsFull [] [(65536, 8192)] [(69632, 4096)] 0 0 4096 0 demo_sp)
      noaccess_base).

(** Exposing a MAP_NORESERVE guard keeps its lazy provenance and the first
    page's existing first-touch charge; the second page is not charged until
    an instruction actually accesses it. *)
Example mprotect_lazy_guard_preserves_backing_provenance :
  check_syscall
    (mkInput 226 [69632; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(69632, 4096)]) mprotect_lazy_guard
  = CheckOk (mprotect_model_next mprotect_lazy_guard 69632 4096) [].
Proof. check_eq. Qed.

Example mprotect_lazy_guard_does_not_eagerly_charge :
  let post := mprotect_model_next mprotect_lazy_guard 69632 4096 in
  m_vm_lazy post = [(65536, 8192)] /\
  m_vm_materialized post = [65536] /\
  vm_backing_used post = 4096%Z.
Proof. cbv zeta. split_conj; check_eq. Qed.

(** ** The read-only downgrade, pinned at the checker

    [mprotect(addr, len, PROT_READ)] over a live rw mapping is the shape
    an allocator reaches for after filling a buffer, and Linux answers it
    with 0 (mm/mprotect.c [do_mprotect_pkey] / [mprotect_fixup]: newflags
    loses VM_WRITE and the mapping stays live and readable).  The model
    declines it, and [Sys/Mm/Mprotect.v] argues why: anonymous memory has
    one representation, which is simultaneously the readable view and the
    writable one, so a readable-not-writable page cannot be encoded.

    These read the checker directly, and the first is the one that
    matters: offering the checker the answer the real kernel gives has
    to yield [CheckUnmodeled], not [CheckOk].
    A spec that widened [mprotect_modeled_b] to "prot is a subset of the
    permissions the range already has" would take that 0 and admit every
    later store to a page Linux has made read-only. *)
Example mprotect_read_only_downgrade_is_unmodeled :
  check_syscall
    (mkInput 226 [65536; 4096; 1 (* PROT_READ *); 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** The declining arm is reached on the ARGUMENT SHAPE, so no offered
    effect rescues it: a zero-fill range is refused for the same reason,
    rather than being rejected as the wrong effect for a modeled call. *)
Example mprotect_read_only_downgrade_with_zeros_is_unmodeled :
  check_syscall
    (mkInput 226 [65536; 4096; 1 (* PROT_READ *); 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(65536, 4096)])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** PROT_READ over a range that is still PROT_NONE is declined too, which
    is worth pinning separately: that range IS in [vm_noaccess], so the
    rw transition's own gate matches on everything but the prot word.  A
    spec that tested containment before the prot would expose the page
    and hand the effect's zero-fill to a program that may not write it. *)
Example mprotect_read_only_over_noaccess_is_unmodeled :
  check_syscall
    (mkInput 226 [69632; 4096; 1 (* PROT_READ *); 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(69632, 4096)]) noaccess_three_pages
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** The positive half at the same prot: the gates ahead of the prot test
    answer for PROT_READ exactly as they do for the modeled rw, because
    Linux takes its zero-length return before validating prot at all.
    Its negative twin is below — a zero-length call admits 0 and nothing
    else. *)
Example mprotect_read_only_zero_length_is_zero :
  check_syscall
    (mkInput 226 [65536; 0; 1 (* PROT_READ *); 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = CheckOk (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384)
               noaccess_base) [].
Proof. check_eq. Qed.

Example mprotect_read_only_zero_length_errno_is_rejected :
  check_syscall
    (mkInput 226 [65536; 0; 1 (* PROT_READ *); 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = CheckReject.
Proof. check_eq. Qed.

(** ** The vdso/vvar pair: declined before the ledger is read

    [__setup_additional_pages] (arch/riscv/kernel/vdso.c:110-150, Linux
    v6.18.46) maps the pair at the top of the mmap search window: the
    four vvar pages at the base of the span [get_unmapped_area] returns
    (:120-130, through [vdso_install_vvar_mapping],
    lib/vdso/datastore.c:99-104, Linux v6.18.46), the text directly above
    them (vdso.c:134-140).  [mprotect_spec] declines an rw request that
    meets the pair before it reads [vm_noaccess] or [vm_maps].

    Linux's answers there, on a kernel without
    CONFIG_MSEAL_SYSTEM_MAPPINGS ([VM_SEALED_SYSMAP] is [VM_NONE],
    include/linux/mm.h:4402-4406, Linux v6.18.46):
    - rw over a vvar page is -EACCES at mm/mprotect.c:960-963 (Linux
      v6.18.46, [do_mprotect_pkey]), before [mprotect_fixup] (:990)
      charges anything: the vvar pages lack VM_MAYWRITE
      (lib/vdso/datastore.c:101-103, Linux v6.18.46);
    - rw over the whole text is 0, or -ENOMEM from [mprotect_fixup]'s
      accounting (mm/mprotect.c:801-808, Linux v6.18.46): the text
      carries VM_MAYWRITE (arch/riscv/kernel/vdso.c:139, Linux v6.18.46),
      every -EINVAL test of [do_mprotect_pkey] passes, and the range is
      the whole VMA, so [vma_modify] neither merges (mm/vma.c:844-845,
      Linux v6.18.46) nor splits (:1664, :1672) and
      [special_mapping_split]'s -EINVAL (mm/mmap.c:1394-1403, Linux
      v6.18.46) is never asked;
    - over part of the text the split is asked, and that -EINVAL is
      Linux's answer; no example below makes that request.

    The ledger below is one no grant produces: it holds the pair's span
    as a PROT_NONE grant, beside the run's first grant one page under
    the pair, so the pair's test is the only one between each request
    and the exposure.  Its budget is zero. *)
Definition mprotect_vdso_pair_held_noaccess : Model :=
  with_vmmaps
    (mkVmMapsFull
      [(23387528564736, 16384); (23387528581120, 8192)]
      [(23387528560640, 4096); (23387528564736, 24576)]
      [(23387528560640, 4096); (23387528564736, 24576)]
      0 0 0 (Z_to_bv 64 mmap_base_min) demo_sp)
    noaccess_base.

(** The pair the test reads is the pair [vm_reserved] holds, at the
    fixture's literal addresses. *)
Example mprotect_vdso_pair_held_noaccess_holds_the_launch_pair :
  vdso_reserved (m_kernel mprotect_vdso_pair_held_noaccess)
    (vdso_top (m_vmmaps mprotect_vdso_pair_held_noaccess))
  = [(23387528564736, 16384); (23387528581120, 8192)] /\
  vm_reserved (m_vmmaps mprotect_vdso_pair_held_noaccess)
  = vdso_reserved (m_kernel mprotect_vdso_pair_held_noaccess)
      (vdso_top (m_vmmaps mprotect_vdso_pair_held_noaccess)).
Proof. split_conj; check_eq. Qed.

(** Linux's -EACCES for the vvar page is declined, not admitted. *)
Example mprotect_vvar_rw_is_unmodeled :
  check_syscall
    (mkInput 226 [23387528564736; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EACCES) [] []) mprotect_vdso_pair_held_noaccess
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** Linux's 0 for the whole text is declined, not admitted. *)
Example mprotect_vdso_text_rw_is_unmodeled :
  check_syscall
    (mkInput 226 [23387528581120; 8192; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) mprotect_vdso_pair_held_noaccess
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** An -EINVAL, which Linux does not answer for the whole text, is not
    admitted either. *)
Example mprotect_vdso_text_rw_einval_is_unmodeled :
  check_syscall
    (mkInput 226 [23387528581120; 8192; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) mprotect_vdso_pair_held_noaccess
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** One page lower, on the run's first grant, the request meets no part
    of the pair and is an ordinary exposure of a PROT_NONE page: over the
    zero budget only the charge's -ENOMEM (mm/mprotect.c:801-808, Linux
    v6.18.46) remains. *)
Example mprotect_under_the_vdso_pair_over_budget_allows_enomem :
  check_syscall
    (mkInput 226 [23387528560640; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] []) mprotect_vdso_pair_held_noaccess
  = CheckOk mprotect_vdso_pair_held_noaccess [].
Proof. check_eq. Qed.

Example mprotect_under_the_vdso_pair_over_budget_rejects_success :
  check_syscall
    (mkInput 226 [23387528560640; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(23387528560640, 4096)]) mprotect_vdso_pair_held_noaccess
  = CheckReject.
Proof. check_eq. Qed.

(** The budget mark is false on the vvar page, where the model declines
    and Linux's -EACCES comes before any charge, and true one page lower,
    a request that differs in [addr] alone. *)
Example mprotect_budget_mark_silent_on_the_vvar_pages :
  mprotect_budget_refused_b 23387528564736 4096 3
    mprotect_vdso_pair_held_noaccess = false.
Proof. check_eq. Qed.

Example mprotect_budget_mark_fires_under_the_vdso_pair :
  mprotect_budget_refused_b 23387528560640 4096 3
    mprotect_vdso_pair_held_noaccess = true.
Proof. check_eq. Qed.
