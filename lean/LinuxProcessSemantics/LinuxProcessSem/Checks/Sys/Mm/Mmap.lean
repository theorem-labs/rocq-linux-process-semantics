import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint
import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Mm.Mmap — the mmap (222), brk (214) and munmap (215) checkers, witnesses, and their proofs

Mirrors `theories/LinuxProcessSem/Checks/Sys/Mm/Mmap.v` — the executable
checkers `check_mmap`, `check_brk` and `check_munmap`, each with its four
proofs — and, in the same file,
`theories/LinuxProcessSem/Checks/Witness/Mm/Mmap.v` — the progress
witnesses `mmap_witness`, `brk_witness` and `munmap_witness`, each with
its `_ok` lemma.  All answer to the relational specs in `Sys/Mm/Mmap.lean`,
which answer to Linux `mm/mmap.c` and `mm/vma.c`.  Not part of the trusted
specification: the checkers' proofs relate them to the specs, and the
proofs are what carry the trust.  The mmap half is K6b's and comes
first; the brk and munmap halves are C-Mm-Mmap-brk-munmap's and follow
the sentinel line at the end of the mmap half.  Rocq orders the three
`check_brk`, `check_mmap`, `check_munmap`; the mmap half stays first
here because K6b landed it.  The header paragraphs below are the mmap
half's; the brk and munmap halves carry their own at the sentinel.

THE BASELINE.  The ticket brief names `f44244ad6b8041aa83053d9ca91e090037ed743b`
as the Rocq this file was read from.  That commit is not an ancestor of
the day branch this file lands on, so the header carries the ancestor
`a71fd38a0857` the rest of the Lean tree pins instead.  Of the two Rocq
files this file mirrors, `Checks/Sys/Mm/Mmap.v` is byte-identical at the
two commits and at 184fa7ead, the day-branch commit this branch is based
on (blob `25416dc808df` at all three);
`Checks/VmMapsDisjoint.v` is NOT (`b32c4db751c1` at f44244ad,
`87e8fa9d6750` at a71fd38a, and `ffc106771d47` once `check_sched_yield_frame`
landed on the day branch, at 184fa7ead) — the hunks between them are
`check_read_frame`, `check_pread64_frame`, `check_openat_frame`,
`check_unlinkat_frame`, the `check_fstat_*_frame` family and
`check_sched_yield_frame`, all after `check_mmap_preserves` (line 1247
in each), which is unchanged.  So
nothing this file read differs, and the identity claim is the narrower
one.  `Checks/Sys/Dispatch.lean`'s header carries the same argument for
`Checks/Sys/Dispatch.v`, which is byte-identical at f44244ad and a71fd38a
(blob `c432551f87e4` at both); 184fa7ead's `393f0d5188d1` adds only
`arm_sched_yield` and its three lemmas (6e7c0d18d, #1162).

THE MAP_FIXED_NOREPLACE ARMS.  They came with the spec twin's arms and
not after them, because a spec arm the checker still declined would
falsify `check_mmap_sound_unmodeled` and `mmap_witness_ok`.  The
occupied branch accepts an effect with every list empty and hands the
model back: `do_mmap`'s `find_vma_intersection` refusal (mm/mmap.c,
Linux v6.18.46) returns before `mmap_region` runs, so neither the
destroyed-range resolution nor a zero list has anything to name.  The
witness tests no ledger, because both ledger sub-cases carry the errno
arm.  What the spec twin's section records of the bit in Linux and in
qemu-user is not repeated.

WHY THE PRESERVES LEMMA IS HERE.  Rocq states `check_mmap_preserves`
in `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, beside the other
arms' lemmas.  `Checks/VmMapsDisjoint.lean` holds the invariant `vm_wf`
and the ledger lemmas (`maps_wf_cons_free`, `maps_wf_subtract`,
`maps_subtract_region_free`) and names no syscall checker, so the lemma
sits beside the checker whose accepted models it walks, and this file
imports the invariant's file for it.  That import is acyclic because
`Checks/VmMapsDisjoint.lean` imports `Checks/Sys/Dispatch.lean` and not
`Checks/Sys/Table.lean`; the arm-level fact `arm_mmap_preserves_vm`,
which names the arm the table holds, lives in
`Checks/VmMapsDisjoint/Arms.lean` for the reason that file's header gives.

THE ACCEPTOR READING, in the order Linux reads the call.  Every kernel
claim below is read at Linux v6.18.46 (commit 1f99e9ab748f).  The
riscv entry `riscv_sys_mmap` (arch/riscv/kernel/sys_riscv.c) refuses an
offset with low bits set with -EINVAL before `ksys_mmap_pgoff`
(mm/mmap.c) is reached — so the offset gate is first, ahead of the
length: on a misaligned offset the checker accepts -EINVAL alone, and
only while the page-rounded length does not wrap, since a wrapping
length is a shape the spec twin declines rather than orders against the
offset.  `do_mmap` (mm/mmap.c, Linux v6.18.46) then answers
`if (!len) return -EINVAL` before `PAGE_ALIGN(len)`, which is the
zero-length gate.  The -EINVAL the fixed arms then commit to at a
misaligned address is what `__get_unmapped_area` answers; `do_mmap`'s
`if (mm->map_count > sysctl_max_map_count) return -ENOMEM` (mm/mmap.c,
Linux v6.18.46) is read before that call, so the commitment holds while
the process is under `vm.max_map_count`.  The spec twin's arms do not
carry that premise — they commit -EINVAL below `alloc_top`
unconditionally — and the false reject at the map-count ceiling is the
one shape `bugs/vm-limit-environment-obligation.md` records for `mmap`;
no fixture reaches it.  Before the alignment gate the checker declines a
range that ends above `alloc_top`: the stack
is in no ledger list, so a ledger-free range up there may be the stack
itself, whose position `Run.valid_sp` quantifies over, and the spec twin
stops rather than pick a layout.  A fixed address of zero is declined
for the reason `Sys/Mm/Mmap.lean` gives: `security_mmap_addr`
(`__get_unmapped_area`'s last test, mm/mmap.c, Linux v6.18.46) answers
by policy there — its baseline `cap_mmap_addr` (security/commoncap.c,
Linux v6.18.46) refuses with -EPERM
only below `dac_mmap_min_addr`, whose default is 4096 and which the
`vm.mmap_min_addr` sysctl moves — and the model carries no policy.  Above
zero the arms answer the default policy alone; the `bugs/` entry #895
landed on the day branch, `mmap-fixed-below-mmap-min-addr-admits-default-policy-alone`,
records what that costs.  (`mmap_min_addr` itself, the maximum of that
value and the LSM floor, is what the searches bound a hint and a length
by; it refuses no address of its own.)

READING A SUCCESS.  `-ENOMEM` is admitted at every modeled shape,
regardless of the ledger, because the kernel can fail to allocate at
any point after the argument gates — the VMA itself (`vm_area_alloc`)
or the maple-tree node its insertion needs (`vma_iter_prealloc`), both
in `__mmap_new_vma`, mm/vma.c, reached from `do_mmap`, mm/mmap.c, through
`__mmap_region`, mm/vma.c, all Linux v6.18.46; page tables are allocated
at fault time, not here — and nothing the model tracks predicts it.  A
non-errno return is a placement, and the checker reads it against the
ledger exactly as the spec's `choose` constrains it.  The effect's zero
list (rw) or unmap list (PROT_NONE) must name exactly the page-rounded
grant: every page of a fresh anonymous mapping reads back zero-filled
(`do_anonymous_page`, mm/memory.c, Linux v6.18.46, backs the first touch
with a zeroed folio or the zero page), and the unmap list is how a
PROT_NONE grant tells the executor the range is unreadable.  `errno_ret_in` is the test that separates the two readings,
and it is complete because a placement the spec admits sits below
`alloc_top`, a whole stack's width under `2^64`, where no errno encodes
(`errno_ret_in_below`).

THE MAP_FIXED RESOLUTIONS.  A MAP_FIXED request over a range the ledger
already owns whole is the `vms_gather_munmap_vmas` /
`vms_clean_up_area` path of `__mmap_prepare` (mm/vma.c, Linux v6.18.46): the old mapping
is torn down before the new VMA is built, and an -ENOMEM after that
teardown leaves the range UNMAPPED (`vms_abort_munmap_vmas`, mm/vma.c,
Linux v6.18.46, does not restore it).  So the contained and spanning arms allow three
resolutions — the errno with the range in place, the placement, and the
errno with the range destroyed — and the checker tells the third from
the first by the unmap list the effect carries, which must name exactly
the request.  A free range is an ordinary grant that names its own
address, and a range that meets one of the image's LOAD reservations is
declined.

HOW THE PROOFS GO.  Each is one walk down the checker's `if` chain
against the spec's, in the shape `Checks/Sys/Kernel/Exit.lean`'s four
proofs set and the mprotect checker's (PR #1065's, on the day branch
and not on this file's base, so a reader at this PR's head will not find
it) widened to a chain of gates: a Bool gate hands the spec's identical
`if` the same hypothesis,
`ite_eq_left`/`ite_eq_right` rewrite it, and the effect match is split
alternative by alternative.  Two facts about that walk
are load-bearing.  The `let`s the spec and the checker both write are
zeta-reduced by one `dsimp only` before anything else, so that the
page-rounded end `bv_unsigned addr + page_round_up_Z (bv_unsigned len)`
is a term both sides share and one `generalize` can name.  And the wrap
gate on that term is never `split`: `two_pow_64` is `2 ^ 64` and a
`split` there sends `whnf` into `Int.decLe` on the closed power, which
dies of `maxRecDepth`; `by_cases` on the proposition with the two `ite`
lemmas is the same case analysis without the evaluation.  The closed
gates each `choose` carries — `0 < a`, the alignment, the ceiling — are
`decide`d Bools in the checker so that `decide_eq_true_eq` reads them
back as the spec's own propositions; the fixed arms' gates are written
in the spec's `!( … == …)` spelling instead, because there the two
sides must be the SAME `if` for the hypothesis to transfer. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## Two arithmetic facts Rocq keeps beside this checker -/

/-- Rocq: `page_round_up_Z_nonneg`.  `omega` reads the division by the
literal `page_size` directly, where Rocq goes through `Z.div_pos`. -/
theorem page_round_up_Z_nonneg (z : Int) (hz : 0 ≤ z) : 0 ≤ page_round_up_Z z := by
  unfold page_round_up_Z page_size
  omega

/-- Rocq: `page_round_up_Z_mono`. -/
theorem page_round_up_Z_mono (a b : Int) (h : a ≤ b) : page_round_up_Z a ≤ page_round_up_Z b := by
  unfold page_round_up_Z page_size
  omega

/-- The `else` side of a `!decide p` gate, read as `p`.  Rocq's
`negb_false_iff` with `Z.leb_le` or `Z.ltb_lt`; stated once because the
fixed arms' ceiling and positivity gates are both spelled that way and
the preserves lemma needs both as propositions. -/
theorem of_not_gate {p : Prop} [Decidable p] (h : ¬((!decide p) = true)) : p :=
  Decidable.byContradiction (fun hn => h (by simp only [decide_eq_false hn, Bool.not_false]))

/-! ## The checker -/

set_option linter.unusedVariables false in
/-- The executable acceptor for `mmap_spec`.  Rocq: `check_mmap`.

`fd` is a parameter and is never read, for the reason `mmap_spec` gives:
the one path answered is `mmap_fd_none`'s, and the file-backed path that
would read it is declined before it could.  The linter is told so here
rather than by renaming the argument away from the Rocq signature. -/
def check_mmap (addr len prot flags fd off : word) (eff : SyscallEffect) (m : Model) :
    check_result :=
  if !(mmap_off_aligned_b off) then
    (if mmap_pglen_ok_b len then check_ret_only eff (errno_ret EINVAL) m [] else CheckUnmodeled)
  else if !(mmap_anon_b flags) then
    CheckUnmodeled
  else if w_is0 len then
    (if mmap_plain_anon_b flags then check_ret_only eff (errno_ret EINVAL) m [] else CheckUnmodeled)
  else if mmap_modeled_b prot flags off then
    match eff with
    | SyscallEffect.mkEffectU r [] zs [] [] [] =>
      if errno_ret_in mmap_errnos r then
        (match zs with
         | [] => CheckOk m []
         | _ :: _ => CheckReject)
      else
        let h := m_vmmaps m
        let nZ := page_round_up_Z (bv_unsigned len)
        let n := Z_to_bv 64 nZ
        if decide (bv_unsigned r % page_size = 0) && decide (0 < bv_unsigned r)
            && decide (bv_unsigned r + nZ ≤ alloc_top h)
            && region_free (h.vm_reserved ++ h.vm_maps) r n
            && mmap_noreserve_backed_ok flags m nZ
            && listNN_eqb zs [(r, n)]
        then CheckOk (with_mmap_backing flags r n
               (with_vmmaps
                 (VmMaps.mkVmMapsFull h.vm_reserved ((r, n) :: h.vm_maps)
                   h.vm_noaccess h.vm_start_brk h.vm_brk h.vm_limit
                   h.vm_mmap_base h.vm_init_sp) m)) []
        else CheckReject
    | _ => CheckReject
  else if mmap_noaccess_b prot flags off then
    match eff with
    | SyscallEffect.mkEffectU r [] [] us [] [] =>
      if errno_ret_in mmap_errnos r then
        (match us with
         | [] => CheckOk m []
         | _ :: _ => CheckReject)
      else
        let h := m_vmmaps m
        let nZ := page_round_up_Z (bv_unsigned len)
        let n := Z_to_bv 64 nZ
        if decide (bv_unsigned r % page_size = 0) && decide (0 < bv_unsigned r)
            && decide (bv_unsigned r + nZ ≤ alloc_top h)
            && region_free (h.vm_reserved ++ h.vm_maps) r n
            && listNN_eqb us [(r, n)]
        then CheckOk (with_mmap_backing flags r n
               (with_vmmaps
                 (VmMaps.mkVmMapsFull h.vm_reserved ((r, n) :: h.vm_maps)
                   ((r, n) :: h.vm_noaccess) h.vm_start_brk
                   h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m)) []
        else CheckReject
    | _ => CheckReject
  else if mmap_fixed_noaccess_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len)
    if two_pow_64 ≤ bv_unsigned addr + nZ then
      if two_pow_64 ≤ nZ then check_ret_only eff (errno_ret ENOMEM) m []
      else if two_pow_64 - page_size < bv_unsigned addr then
        CheckUnmodeled
      else if bv_unsigned addr % page_size = 0 then
        if bv_unsigned addr + nZ = two_pow_64 then
          CheckUnmodeled
        else check_ret_only eff (errno_ret ENOMEM) m []
      else
        CheckUnmodeled
    else
      let h := m_vmmaps m
      if !(bv_unsigned addr + nZ ≤ alloc_top h) then CheckUnmodeled
      else if !(bv_unsigned addr % page_size == 0) then check_ret_only eff (errno_ret EINVAL) m []
      else if !(0 < bv_unsigned addr) then CheckUnmodeled
      else
      let n := Z_to_bv 64 nZ
      if region_free h.vm_reserved addr n && map_contains h.vm_maps addr n then
        match eff with
        | SyscallEffect.mkEffectU r [] [] us [] [] =>
          if errno_ret_in mmap_errnos r then
            (match us with
             | [] => CheckOk m []
             | _ :: _ =>
               if listNN_eqb us [(addr, n)]
               then CheckOk (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) []
               else CheckReject)
          else if bv_eqb r addr && listNN_eqb us [(addr, n)]
          then CheckOk (with_mmap_replacement flags addr n
                 (with_vmmaps (VmMaps.mkVmMapsFull h.vm_reserved h.vm_maps
                   ((addr, n) :: maps_subtract h.vm_noaccess
                                   (bv_unsigned addr)
                                   (bv_unsigned addr + bv_unsigned n))
                   h.vm_start_brk h.vm_brk h.vm_limit
                   h.vm_mmap_base h.vm_init_sp) m)) []
          else CheckReject
        | _ => CheckReject
      else if region_free (h.vm_reserved ++ h.vm_maps) addr n then
        match eff with
        | SyscallEffect.mkEffectU r [] [] us [] [] =>
          if errno_ret_in mmap_errnos r then
            (match us with
             | [] => CheckOk m []
             | _ :: _ => CheckReject)
          else if bv_eqb r addr && listNN_eqb us [(addr, n)]
          then CheckOk (with_mmap_backing flags addr n
                 (with_vmmaps (VmMaps.mkVmMapsFull h.vm_reserved ((addr, n) :: h.vm_maps)
                   ((addr, n) :: h.vm_noaccess) h.vm_start_brk
                   h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m)) []
          else CheckReject
        | _ => CheckReject
      else if region_free h.vm_reserved addr n then
        match eff with
        | SyscallEffect.mkEffectU r [] [] us [] [] =>
          if errno_ret_in mmap_errnos r then
            (match us with
             | [] => CheckOk m []
             | _ :: _ =>
               if listNN_eqb us [(addr, n)]
               then CheckOk (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) []
               else CheckReject)
          else if bv_eqb r addr && listNN_eqb us [(addr, n)]
          then CheckOk (with_mmap_replacement flags addr n
                 (with_vmmaps (mmap_fixed_noaccess_span_next h addr n) m)) []
          else CheckReject
        | _ => CheckReject
      else CheckUnmodeled
  else if mmap_fixed_rw_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len)
    if two_pow_64 ≤ bv_unsigned addr + nZ then
      if two_pow_64 ≤ nZ then check_ret_only eff (errno_ret ENOMEM) m []
      else if two_pow_64 - page_size < bv_unsigned addr then
        CheckUnmodeled
      else if bv_unsigned addr % page_size = 0 then
        if bv_unsigned addr + nZ = two_pow_64 then
          CheckUnmodeled
        else check_ret_only eff (errno_ret ENOMEM) m []
      else
        CheckUnmodeled
    else
      let h := m_vmmaps m
      if !(bv_unsigned addr + nZ ≤ alloc_top h) then CheckUnmodeled
      else if !(bv_unsigned addr % page_size == 0) then check_ret_only eff (errno_ret EINVAL) m []
      else if !(0 < bv_unsigned addr) then CheckUnmodeled
      else
      let n := Z_to_bv 64 nZ
      if region_free h.vm_reserved addr n && map_contains h.vm_maps addr n then
        match eff with
        | SyscallEffect.mkEffectU r [] zs us [] [] =>
          if errno_ret_in mmap_errnos r then
            (match zs with
             | [] =>
               (match us with
                | [] => CheckOk m []
                | _ :: _ =>
                  if listNN_eqb us [(addr, n)]
                  then CheckOk (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) []
                  else CheckReject)
             | _ :: _ => CheckReject)
          else
            (match us with
             | [] =>
               if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                   && mmap_fixed_rw_budget_ok flags m addr n
               then CheckOk (with_mmap_replacement flags addr n
                      (with_vmmaps (mmap_fixed_rw_next h addr n) m)) []
               else CheckReject
             | _ :: _ => CheckReject)
        | _ => CheckReject
      else if region_free (h.vm_reserved ++ h.vm_maps) addr n then
        match eff with
        | SyscallEffect.mkEffectU r [] zs [] [] [] =>
          if errno_ret_in mmap_errnos r then
            (match zs with
             | [] => CheckOk m []
             | _ :: _ => CheckReject)
          else if bv_eqb r addr && listNN_eqb zs [(addr, n)]
              && mmap_noreserve_backed_ok flags m nZ
          then CheckOk (with_mmap_backing flags addr n
                 (with_vmmaps (VmMaps.mkVmMapsFull h.vm_reserved ((addr, n) :: h.vm_maps)
                   h.vm_noaccess h.vm_start_brk h.vm_brk h.vm_limit
                   h.vm_mmap_base h.vm_init_sp) m)) []
          else CheckReject
        | _ => CheckReject
      else if region_free h.vm_reserved addr n then
        match eff with
        | SyscallEffect.mkEffectU r [] zs us [] [] =>
          if errno_ret_in mmap_errnos r then
            (match zs with
             | [] =>
               (match us with
                | [] => CheckOk m []
                | _ :: _ =>
                  if listNN_eqb us [(addr, n)]
                  then CheckOk (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) []
                  else CheckReject)
             | _ :: _ => CheckReject)
          else
            (match us with
             | [] =>
               if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                   && mmap_fixed_rw_span_budget_ok flags m addr n
               then CheckOk (with_mmap_replacement flags addr n
                      (with_vmmaps (mmap_fixed_rw_span_next h addr n) m)) []
               else CheckReject
             | _ :: _ => CheckReject)
        | _ => CheckReject
      else CheckUnmodeled
  else if mmap_noreplace_noaccess_b prot flags off then
    -- MAP_FIXED_NOREPLACE, PROT_NONE: the MAP_FIXED argument gate, then one
    -- split on the ledger — the free-range reservation, or -EEXIST beside
    -- the environment errno
    let nZ := page_round_up_Z (bv_unsigned len)
    if two_pow_64 ≤ bv_unsigned addr + nZ then
      if two_pow_64 ≤ nZ then check_ret_only eff (errno_ret ENOMEM) m []
      else if two_pow_64 - page_size < bv_unsigned addr then
        CheckUnmodeled
      else if bv_unsigned addr % page_size = 0 then
        if bv_unsigned addr + nZ = two_pow_64 then
          CheckUnmodeled
        else check_ret_only eff (errno_ret ENOMEM) m []
      else
        CheckUnmodeled
    else
      let h := m_vmmaps m
      if !(bv_unsigned addr + nZ ≤ alloc_top h) then CheckUnmodeled
      else if !(bv_unsigned addr % page_size == 0) then check_ret_only eff (errno_ret EINVAL) m []
      else if !(0 < bv_unsigned addr) then CheckUnmodeled
      else
      let n := Z_to_bv 64 nZ
      if region_free (h.vm_reserved ++ h.vm_maps) addr n then
        match eff with
        | SyscallEffect.mkEffectU r [] [] us [] [] =>
          if errno_ret_in mmap_errnos r then
            (match us with
             | [] => CheckOk m []
             | _ :: _ => CheckReject)
          else if bv_eqb r addr && listNN_eqb us [(addr, n)]
          then CheckOk (with_mmap_backing flags addr n
                 (with_vmmaps (VmMaps.mkVmMapsFull h.vm_reserved ((addr, n) :: h.vm_maps)
                   ((addr, n) :: h.vm_noaccess) h.vm_start_brk
                   h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m)) []
          else CheckReject
        | _ => CheckReject
      else
        match eff with
        | SyscallEffect.mkEffectU r [] [] [] [] [] =>
          if errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST)
          then CheckOk m [] else CheckReject
        | _ => CheckReject
  else if mmap_noreplace_rw_b prot flags off then
    -- MAP_FIXED_NOREPLACE, rw: the same gate and split, with the rw
    -- free-range grant and its budget conjunct
    let nZ := page_round_up_Z (bv_unsigned len)
    if two_pow_64 ≤ bv_unsigned addr + nZ then
      if two_pow_64 ≤ nZ then check_ret_only eff (errno_ret ENOMEM) m []
      else if two_pow_64 - page_size < bv_unsigned addr then
        CheckUnmodeled
      else if bv_unsigned addr % page_size = 0 then
        if bv_unsigned addr + nZ = two_pow_64 then
          CheckUnmodeled
        else check_ret_only eff (errno_ret ENOMEM) m []
      else
        CheckUnmodeled
    else
      let h := m_vmmaps m
      if !(bv_unsigned addr + nZ ≤ alloc_top h) then CheckUnmodeled
      else if !(bv_unsigned addr % page_size == 0) then check_ret_only eff (errno_ret EINVAL) m []
      else if !(0 < bv_unsigned addr) then CheckUnmodeled
      else
      let n := Z_to_bv 64 nZ
      if region_free (h.vm_reserved ++ h.vm_maps) addr n then
        match eff with
        | SyscallEffect.mkEffectU r [] zs [] [] [] =>
          if errno_ret_in mmap_errnos r then
            (match zs with
             | [] => CheckOk m []
             | _ :: _ => CheckReject)
          else if bv_eqb r addr && listNN_eqb zs [(addr, n)]
              && mmap_noreserve_backed_ok flags m nZ
          then CheckOk (with_mmap_backing flags addr n
                 (with_vmmaps (VmMaps.mkVmMapsFull h.vm_reserved ((addr, n) :: h.vm_maps)
                   h.vm_noaccess h.vm_start_brk h.vm_brk h.vm_limit
                   h.vm_mmap_base h.vm_init_sp) m)) []
          else CheckReject
        | _ => CheckReject
      else
        match eff with
        | SyscallEffect.mkEffectU r [] [] [] [] [] =>
          if errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST)
          then CheckOk m [] else CheckReject
        | _ => CheckReject
  else CheckUnmodeled



/-! ## The four proofs

Each is one walk down the two `if` chains.  The outer gates are opened
with `by_cases` on the gate's own proposition and the two `ite` lemmas,
at the hypothesis and the goal at once; `split at h` is kept for the
effect match and the small conditions inside one arm.  `split` rewrites
with `simp`, whose step budget is spent on the size of the term it walks,
and the whole checker is over it: on the first gate `split at h` fails
with `maximum number of steps exceeded`, where `rw` with the same
hypothesis is one abstraction.  This is the shape the mprotect checker's
proofs (PR #1065, on the day branch ahead of this base) have only for the
wrap gate, applied to every gate. -/

/-- Every `CheckOk` the checker returns is a run the spec admits, with the
same model and the same (empty) event list.  Rocq: `check_mmap_sound_ok`. -/
theorem check_mmap_sound_ok (addr len prot flags fd off : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : check_mmap addr len prot flags fd off eff m = CheckOk m' evs) :
    mmap_spec addr len prot flags fd off i m (Ok eff m' evs) := by
  unfold check_mmap at h
  unfold mmap_spec
  dsimp only at h
  dsimp only
  generalize bv_unsigned addr + page_round_up_Z (bv_unsigned len) = X at h ⊢
  -- the offset gate, then the anonymous-only gate, then the zero length
  by_cases hg1 : (!mmap_off_aligned_b off) = true
  · rw [ite_eq_left hg1] at h ⊢
    -- `cases`, not `by_cases`: the gate's `Decidable` instance is found by
    -- unfolding `mmap_pglen_ok_b` to its `decide` on `two_pow_64`, and the
    -- instance check then evaluates the closed power (maxRecDepth)
    cases hp : mmap_pglen_ok_b len
    · rw [hp, ite_eq_right Bool.false_ne_true] at h
      cases h
    · rw [hp, ite_eq_left rfl] at h
      rw [ite_eq_left rfl]
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
  rw [ite_eq_right hg1] at h ⊢
  by_cases hg2 : (!mmap_anon_b flags) = true
  · rw [ite_eq_left hg2] at h
    cases h
  rw [ite_eq_right hg2] at h ⊢
  by_cases hg3 : w_is0 len = true
  · rw [ite_eq_left hg3] at h ⊢
    by_cases hp : mmap_plain_anon_b flags = true
    · rw [ite_eq_left hp] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    · rw [ite_eq_right hp] at h
      cases h
  rw [ite_eq_right hg3] at h ⊢
  -- the plain rw grant
  by_cases hp1 : mmap_modeled_b prot flags off = true
  · rw [ite_eq_left hp1] at h ⊢
    split at h
    · rename_i r zs
      split at h
      · rename_i he
        obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
        split at h
        · cases h
          apply alt_l
          apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
          exact pure_ok _ i _
        · cases h
      · split at h
        · rename_i hC
          simp only [Bool.and_eq_true, decide_eq_true_eq, listNN_eqb_eq] at hC
          obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, rfl⟩ := hC
          cases h
          apply alt_r
          apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
          apply bind_ok0 _ _ i m r m _ _ _ (choose_ok _ r i m ⟨h1, h2, h3, h4, h5⟩)
          apply bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
          exact pure_ok _ i _
        · cases h
    · cases h
  rw [ite_eq_right hp1] at h ⊢
  -- the plain PROT_NONE reservation
  by_cases hp2 : mmap_noaccess_b prot flags off = true
  · rw [ite_eq_left hp2] at h ⊢
    split at h
    · rename_i r us
      split at h
      · rename_i he
        obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
        split at h
        · cases h
          apply alt_l
          apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
          exact pure_ok _ i _
        · cases h
      · split at h
        · rename_i hC
          simp only [Bool.and_eq_true, decide_eq_true_eq, listNN_eqb_eq] at hC
          obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, rfl⟩ := hC
          cases h
          apply alt_r
          apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
          apply bind_ok0 _ _ i m r m _ _ _ (choose_ok _ r i m ⟨h1, h2, h3, h4⟩)
          apply bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
          exact pure_ok _ i _
        · cases h
    · cases h
  rw [ite_eq_right hp2] at h ⊢
  -- MAP_FIXED with PROT_NONE
  by_cases hp3 : mmap_fixed_noaccess_b prot flags off = true
  · rw [ite_eq_left hp3] at h ⊢
    by_cases hg : two_pow_64 ≤ X
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : X = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals first | cases h | obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h; exact pure_ok _ i _
    rw [ite_eq_right hg] at h ⊢
    apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
    by_cases hc : (!decide (X ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc] at h
      cases h
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz] at h
      cases h
    rw [ite_eq_right hz] at h ⊢
    by_cases hk : (region_free (m_vmmaps m).vm_reserved addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        && map_contains (m_vmmaps m).vm_maps addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) = true
    · -- contained
      rw [ite_eq_left hk] at h ⊢
      split at h
      · rename_i r us
        split at h
        · rename_i he
          obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
          split at h
          · cases h
            apply alt_l
            apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
            exact pure_ok _ i _
          · split at h
            · rename_i hu
              rw [listNN_eqb_eq] at hu
              cases hu
              cases h
              apply alt_r
              apply alt_r
              apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
              apply bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
              exact pure_ok _ i _
            · cases h
        · split at h
          · rename_i hC
            rw [Bool.and_eq_true, bv_eqb_eq, listNN_eqb_eq] at hC
            obtain ⟨hr, rfl⟩ := hC
            cases h
            rw [hr]
            apply alt_r
            apply alt_l
            apply bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
            exact pure_ok _ i _
          · cases h
      · cases h
    rw [ite_eq_right hk] at h ⊢
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- free range
      rw [ite_eq_left hf] at h ⊢
      split at h
      · rename_i r us
        split at h
        · rename_i he
          obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
          split at h
          · cases h
            apply alt_l
            apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
            exact pure_ok _ i _
          · cases h
        · split at h
          · rename_i hC
            rw [Bool.and_eq_true, bv_eqb_eq, listNN_eqb_eq] at hC
            obtain ⟨hr, rfl⟩ := hC
            cases h
            rw [hr]
            apply alt_r
            apply bind_ok0 _ _ i m addr m _ _ _ (choose_ok (fun a => a = addr) addr i m rfl)
            apply bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
            exact pure_ok _ i _
          · cases h
      · cases h
    rw [ite_eq_right hf] at h ⊢
    by_cases hs : region_free (m_vmmaps m).vm_reserved addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- spanning
      rw [ite_eq_left hs] at h ⊢
      split at h
      · rename_i r us
        split at h
        · rename_i he
          obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
          split at h
          · cases h
            apply alt_l
            apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
            exact pure_ok _ i _
          · split at h
            · rename_i hu
              rw [listNN_eqb_eq] at hu
              cases hu
              cases h
              apply alt_r
              apply alt_r
              apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
              apply bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
              exact pure_ok _ i _
            · cases h
        · split at h
          · rename_i hC
            rw [Bool.and_eq_true, bv_eqb_eq, listNN_eqb_eq] at hC
            obtain ⟨hr, rfl⟩ := hC
            cases h
            rw [hr]
            apply alt_r
            apply alt_l
            apply bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
            exact pure_ok _ i _
          · cases h
      · cases h
    rw [ite_eq_right hs] at h
    cases h
  rw [ite_eq_right hp3] at h ⊢
  -- MAP_FIXED with rw
  by_cases hp4 : mmap_fixed_rw_b prot flags off = true
  · rw [ite_eq_left hp4] at h ⊢
    by_cases hg : two_pow_64 ≤ X
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : X = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals first | cases h | obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h; exact pure_ok _ i _
    rw [ite_eq_right hg] at h ⊢
    apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
    by_cases hc : (!decide (X ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc] at h
      cases h
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz] at h
      cases h
    rw [ite_eq_right hz] at h ⊢
    by_cases hk : (region_free (m_vmmaps m).vm_reserved addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        && map_contains (m_vmmaps m).vm_maps addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) = true
    · -- contained
      rw [ite_eq_left hk] at h ⊢
      split at h
      · rename_i r zs us
        split at h
        · rename_i he
          obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
          split at h
          · split at h
            · cases h
              apply alt_l
              apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
              exact pure_ok _ i _
            · split at h
              · rename_i hu
                rw [listNN_eqb_eq] at hu
                cases hu
                cases h
                apply alt_r
                apply alt_r
                apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
                apply bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
                exact pure_ok _ i _
              · cases h
          · cases h
        · split at h
          · split at h
            · rename_i hC
              rw [Bool.and_eq_true, Bool.and_eq_true, bv_eqb_eq, listNN_eqb_eq] at hC
              obtain ⟨⟨hr, rfl⟩, hbud⟩ := hC
              cases h
              rw [hr]
              apply alt_r
              apply alt_l
              apply bind_ok0 _ _ i m () m _ _ _ (choose_ok _ () i m hbud)
              apply bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
              exact pure_ok _ i _
            · cases h
          · cases h
      · cases h
    rw [ite_eq_right hk] at h ⊢
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- free range
      rw [ite_eq_left hf] at h ⊢
      split at h
      · rename_i r zs
        split at h
        · rename_i he
          obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
          split at h
          · cases h
            apply alt_l
            apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
            exact pure_ok _ i _
          · cases h
        · split at h
          · rename_i hC
            rw [Bool.and_eq_true, Bool.and_eq_true, bv_eqb_eq, listNN_eqb_eq] at hC
            obtain ⟨⟨hr, rfl⟩, hbud⟩ := hC
            cases h
            rw [hr]
            apply alt_r
            apply bind_ok0 _ _ i m addr m _ _ _
              (choose_ok (fun a => a = addr
                 ∧ mmap_noreserve_backed_ok flags m (page_round_up_Z (bv_unsigned len)) = true)
                addr i m ⟨rfl, hbud⟩)
            apply bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
            exact pure_ok _ i _
          · cases h
      · cases h
    rw [ite_eq_right hf] at h ⊢
    by_cases hs : region_free (m_vmmaps m).vm_reserved addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- spanning
      rw [ite_eq_left hs] at h ⊢
      split at h
      · rename_i r zs us
        split at h
        · rename_i he
          obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
          split at h
          · split at h
            · cases h
              apply alt_l
              apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
              exact pure_ok _ i _
            · split at h
              · rename_i hu
                rw [listNN_eqb_eq] at hu
                cases hu
                cases h
                apply alt_r
                apply alt_r
                apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
                apply bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
                exact pure_ok _ i _
              · cases h
          · cases h
        · split at h
          · split at h
            · rename_i hC
              rw [Bool.and_eq_true, Bool.and_eq_true, bv_eqb_eq, listNN_eqb_eq] at hC
              obtain ⟨⟨hr, rfl⟩, hbud⟩ := hC
              cases h
              rw [hr]
              apply alt_r
              apply alt_l
              apply bind_ok0 _ _ i m () m _ _ _ (choose_ok _ () i m hbud)
              apply bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
              exact pure_ok _ i _
            · cases h
          · cases h
      · cases h
    rw [ite_eq_right hs] at h
    cases h
  rw [ite_eq_right hp4] at h ⊢
  -- MAP_FIXED_NOREPLACE with PROT_NONE: the fixed gate, then one ledger split
  by_cases hp5 : mmap_noreplace_noaccess_b prot flags off = true
  · rw [ite_eq_left hp5] at h ⊢
    by_cases hg : two_pow_64 ≤ X
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : X = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals first | cases h | obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h; exact pure_ok _ i _
    rw [ite_eq_right hg] at h ⊢
    apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
    by_cases hc : (!decide (X ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc] at h
      cases h
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz] at h
      cases h
    rw [ite_eq_right hz] at h ⊢
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- free range
      rw [ite_eq_left hf] at h ⊢
      split at h
      · rename_i r us
        split at h
        · rename_i he
          obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
          split at h
          · cases h
            apply alt_l
            apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
            exact pure_ok _ i _
          · cases h
        · split at h
          · rename_i hC
            rw [Bool.and_eq_true, bv_eqb_eq, listNN_eqb_eq] at hC
            obtain ⟨hr, rfl⟩ := hC
            cases h
            rw [hr]
            apply alt_r
            apply bind_ok0 _ _ i m addr m _ _ _ (choose_ok (fun a => a = addr) addr i m rfl)
            apply bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
            exact pure_ok _ i _
          · cases h
      · cases h
    -- occupied: the environment errno or -EEXIST, the model untouched
    rw [ite_eq_right hf] at h ⊢
    split at h
    · rename_i r
      split at h
      · rename_i he
        rw [Bool.or_eq_true] at he
        rcases he with he | he
        · obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
          cases h
          apply alt_l
          apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
          exact pure_ok _ i _
        · rw [bv_eqb_eq] at he
          subst he
          cases h
          apply alt_r
          exact pure_ok _ i _
      · cases h
    · cases h
  rw [ite_eq_right hp5] at h ⊢
  -- MAP_FIXED_NOREPLACE with rw
  by_cases hp6 : mmap_noreplace_rw_b prot flags off = true
  · rw [ite_eq_left hp6] at h ⊢
    by_cases hg : two_pow_64 ≤ X
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : X = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals first | cases h | obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h; exact pure_ok _ i _
    rw [ite_eq_right hg] at h ⊢
    apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
    by_cases hc : (!decide (X ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc] at h
      cases h
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz] at h
      cases h
    rw [ite_eq_right hz] at h ⊢
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- free range
      rw [ite_eq_left hf] at h ⊢
      split at h
      · rename_i r zs
        split at h
        · rename_i he
          obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
          split at h
          · cases h
            apply alt_l
            apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
            exact pure_ok _ i _
          · cases h
        · split at h
          · rename_i hC
            rw [Bool.and_eq_true, Bool.and_eq_true, bv_eqb_eq, listNN_eqb_eq] at hC
            obtain ⟨⟨hr, rfl⟩, hbud⟩ := hC
            cases h
            rw [hr]
            apply alt_r
            apply bind_ok0 _ _ i m addr m _ _ _
              (choose_ok (fun a => a = addr
                 ∧ mmap_noreserve_backed_ok flags m (page_round_up_Z (bv_unsigned len)) = true)
                addr i m ⟨rfl, hbud⟩)
            apply bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
            exact pure_ok _ i _
          · cases h
      · cases h
    -- occupied: the environment errno or -EEXIST, the model untouched
    rw [ite_eq_right hf] at h ⊢
    split at h
    · rename_i r
      split at h
      · rename_i he
        rw [Bool.or_eq_true] at he
        rcases he with he | he
        · obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
          cases h
          apply alt_l
          apply bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hin)
          exact pure_ok _ i _
        · rw [bv_eqb_eq] at he
          subst he
          cases h
          apply alt_r
          exact pure_ok _ i _
      · cases h
    · cases h
  rw [ite_eq_right hp6] at h
  cases h

/-- Every `CheckUnmodeled` the checker returns is a run the spec leaves
unmodeled.  Rocq: `check_mmap_sound_unmodeled`. -/
theorem check_mmap_sound_unmodeled (addr len prot flags fd off : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (h : check_mmap addr len prot flags fd off eff m = CheckUnmodeled) :
    mmap_spec addr len prot flags fd off i m Unmodeled := by
  unfold check_mmap at h
  unfold mmap_spec
  dsimp only at h
  dsimp only
  generalize bv_unsigned addr + page_round_up_Z (bv_unsigned len) = X at h ⊢
  by_cases hg1 : (!mmap_off_aligned_b off) = true
  · rw [ite_eq_left hg1] at h ⊢
    cases hp : mmap_pglen_ok_b len
    · rw [ite_eq_right Bool.false_ne_true]
      exact unmodeled_intro i m
    · rw [hp, ite_eq_left rfl] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  rw [ite_eq_right hg1] at h ⊢
  by_cases hg2 : (!mmap_anon_b flags) = true
  · rw [ite_eq_left hg2]
    exact unmodeled_intro i m
  rw [ite_eq_right hg2] at h ⊢
  by_cases hg3 : w_is0 len = true
  · rw [ite_eq_left hg3] at h ⊢
    cases hp : mmap_plain_anon_b flags
    · rw [ite_eq_right Bool.false_ne_true]
      exact unmodeled_intro i m
    · rw [hp, ite_eq_left rfl] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  rw [ite_eq_right hg3] at h ⊢
  -- the two placement arms never decline past their gate
  by_cases hp1 : mmap_modeled_b prot flags off = true
  · rw [ite_eq_left hp1] at h
    exfalso
    split at h
    · split at h
      · split at h <;> cases h
      · split at h <;> cases h
    · cases h
  rw [ite_eq_right hp1] at h ⊢
  by_cases hp2 : mmap_noaccess_b prot flags off = true
  · rw [ite_eq_left hp2] at h
    exfalso
    split at h
    · split at h
      · split at h <;> cases h
      · split at h <;> cases h
    · cases h
  rw [ite_eq_right hp2] at h ⊢
  -- MAP_FIXED with PROT_NONE: the ceiling, the non-positive address, the reservations
  by_cases hp3 : mmap_fixed_noaccess_b prot flags off = true
  · rw [ite_eq_left hp3] at h ⊢
    by_cases hg : two_pow_64 ≤ X
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : X = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals first | exact unmodeled_intro i m | exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    rw [ite_eq_right hg] at h ⊢
    apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
    by_cases hc : (!decide (X ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc]
      exact unmodeled_intro i m
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz]
      exact unmodeled_intro i m
    rw [ite_eq_right hz] at h ⊢
    by_cases hk : (region_free (m_vmmaps m).vm_reserved addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        && map_contains (m_vmmaps m).vm_maps addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) = true
    · rw [ite_eq_left hk] at h
      exfalso
      split at h
      · split at h
        · split at h
          · cases h
          · split at h <;> cases h
        · split at h <;> cases h
      · cases h
    rw [ite_eq_right hk] at h ⊢
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hf] at h
      exfalso
      split at h
      · split at h
        · split at h <;> cases h
        · split at h <;> cases h
      · cases h
    rw [ite_eq_right hf] at h ⊢
    by_cases hs : region_free (m_vmmaps m).vm_reserved addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hs] at h
      exfalso
      split at h
      · split at h
        · split at h
          · cases h
          · split at h <;> cases h
        · split at h <;> cases h
      · cases h
    rw [ite_eq_right hs]
    exact unmodeled_intro i m
  rw [ite_eq_right hp3] at h ⊢
  -- MAP_FIXED with rw: the same three declines
  by_cases hp4 : mmap_fixed_rw_b prot flags off = true
  · rw [ite_eq_left hp4] at h ⊢
    by_cases hg : two_pow_64 ≤ X
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : X = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals first | exact unmodeled_intro i m | exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    rw [ite_eq_right hg] at h ⊢
    apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
    by_cases hc : (!decide (X ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc]
      exact unmodeled_intro i m
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz]
      exact unmodeled_intro i m
    rw [ite_eq_right hz] at h ⊢
    by_cases hk : (region_free (m_vmmaps m).vm_reserved addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        && map_contains (m_vmmaps m).vm_maps addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) = true
    · rw [ite_eq_left hk] at h
      exfalso
      split at h
      · split at h
        · split at h
          · split at h
            · cases h
            · split at h <;> cases h
          · cases h
        · split at h
          · split at h <;> cases h
          · cases h
      · cases h
    rw [ite_eq_right hk] at h ⊢
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hf] at h
      exfalso
      split at h
      · split at h
        · split at h <;> cases h
        · split at h <;> cases h
      · cases h
    rw [ite_eq_right hf] at h ⊢
    by_cases hs : region_free (m_vmmaps m).vm_reserved addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hs] at h
      exfalso
      split at h
      · split at h
        · split at h
          · split at h
            · cases h
            · split at h <;> cases h
          · cases h
        · split at h
          · split at h <;> cases h
          · cases h
      · cases h
    rw [ite_eq_right hs]
    exact unmodeled_intro i m
  rw [ite_eq_right hp4] at h ⊢
  -- MAP_FIXED_NOREPLACE, either prot: the ceiling and the non-positive
  -- address; both ledger sub-cases answer
  by_cases hp5 : mmap_noreplace_noaccess_b prot flags off = true
  · rw [ite_eq_left hp5] at h ⊢
    by_cases hg : two_pow_64 ≤ X
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : X = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals first | exact unmodeled_intro i m | exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    rw [ite_eq_right hg] at h ⊢
    apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
    by_cases hc : (!decide (X ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc]
      exact unmodeled_intro i m
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz]
      exact unmodeled_intro i m
    rw [ite_eq_right hz] at h
    exfalso
    split at h
    · split at h
      · split at h
        · split at h <;> cases h
        · split at h <;> cases h
      · cases h
    · split at h
      · split at h <;> cases h
      · cases h
  rw [ite_eq_right hp5] at h ⊢
  by_cases hp6 : mmap_noreplace_rw_b prot flags off = true
  · rw [ite_eq_left hp6] at h ⊢
    by_cases hg : two_pow_64 ≤ X
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : X = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals first | exact unmodeled_intro i m | exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    rw [ite_eq_right hg] at h ⊢
    apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
    by_cases hc : (!decide (X ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc]
      exact unmodeled_intro i m
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz]
      exact unmodeled_intro i m
    rw [ite_eq_right hz] at h
    exfalso
    split at h
    · split at h
      · split at h
        · split at h <;> cases h
        · split at h <;> cases h
      · cases h
    · split at h
      · split at h <;> cases h
      · cases h
  rw [ite_eq_right hp6]
  exact unmodeled_intro i m

/-- Every run the spec admits is one the checker accepts, with the same
model and the same (empty) event list.  Rocq: `check_mmap_complete_ok`.

The one fact the spec's `choose` does not hand over is that a placement
is no errno: `errno_ret_in_below` reads it off the ceiling, since a grant
ending at or below `alloc_top` starts a stack's width under `2^64`
(`alloc_top_room`), and the fixed arms' ceiling gate says the same of
`addr`. -/
theorem check_mmap_complete_ok (addr len prot flags fd off : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : mmap_spec addr len prot flags fd off i m (Ok eff m' evs)) :
    check_mmap addr len prot flags fd off eff m = CheckOk m' evs := by
  unfold mmap_spec at h
  unfold check_mmap
  dsimp only at h
  dsimp only
  have hnz := page_round_up_Z_nonneg _ (word_unsigned_range len).1
  have hroom := alloc_top_room (m_vmmaps m)
  unfold stack_max_size at hroom
  by_cases hg1 : (!mmap_off_aligned_b off) = true
  · rw [ite_eq_left hg1] at h ⊢
    cases hp : mmap_pglen_ok_b len
    · rw [hp, ite_eq_right Bool.false_ne_true] at h
      have h' : Ok eff m' evs = Unmodeled := h
      cases h'
    · rw [hp, ite_eq_left rfl] at h
      rw [ite_eq_left rfl]
      have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
      cases h'
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  rw [ite_eq_right hg1] at h ⊢
  by_cases hg2 : (!mmap_anon_b flags) = true
  · rw [ite_eq_left hg2] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  rw [ite_eq_right hg2] at h ⊢
  by_cases hg3 : w_is0 len = true
  · rw [ite_eq_left hg3] at h ⊢
    cases hp : mmap_plain_anon_b flags
    · rw [hp, ite_eq_right Bool.false_ne_true] at h
      have h' : Ok eff m' evs = Unmodeled := h
      cases h'
    · rw [hp, ite_eq_left rfl] at h
      rw [ite_eq_left rfl]
      have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
      cases h'
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  rw [ite_eq_right hg3] at h ⊢
  -- the plain rw grant
  by_cases hp1 : mmap_modeled_b prot flags off = true
  · rw [ite_eq_left hp1] at h ⊢
    rcases (alt_iff _ _ i m _).mp h with h | h
    · obtain ⟨e, hin, he⟩ := (bind_choose_iff _ _ i m _).mp h
      have he' : Ok eff m' evs
          = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [] [] []) m [] := he
      cases he'
      dsimp only
      rw [ite_eq_left (errno_ret_in_intro _ _ hin)]
    · have h := (bind_get_model_iff _ i m _).mp h
      obtain ⟨a, ⟨h1, h2, h3, h4, h5⟩, h⟩ := (bind_choose_iff _ _ i m _).mp h
      have h := (bind_modify_iff _ _ i m _).mp h
      have h' : Ok eff m' evs = Ok (SyscallEffect.mkEffectU a [] [(a, _)] [] [] []) _ [] := h
      cases h'
      dsimp only
      have hlow : bv_unsigned a ≤ two_pow_64 - 4096 := by omega
      rw [errno_ret_in_below mmap_errnos a (by decide) hlow, ite_eq_right Bool.false_ne_true,
        ite_eq_left]
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨decide_eq_true h1, decide_eq_true h2⟩, decide_eq_true h3⟩, h4⟩, h5⟩,
        (listNN_eqb_eq _ _).mpr rfl⟩
  rw [ite_eq_right hp1] at h ⊢
  -- the plain PROT_NONE reservation
  by_cases hp2 : mmap_noaccess_b prot flags off = true
  · rw [ite_eq_left hp2] at h ⊢
    rcases (alt_iff _ _ i m _).mp h with h | h
    · obtain ⟨e, hin, he⟩ := (bind_choose_iff _ _ i m _).mp h
      have he' : Ok eff m' evs
          = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [] [] []) m [] := he
      cases he'
      dsimp only
      rw [ite_eq_left (errno_ret_in_intro _ _ hin)]
    · have h := (bind_get_model_iff _ i m _).mp h
      obtain ⟨a, ⟨h1, h2, h3, h4⟩, h⟩ := (bind_choose_iff _ _ i m _).mp h
      have h := (bind_modify_iff _ _ i m _).mp h
      have h' : Ok eff m' evs = Ok (SyscallEffect.mkEffectU a [] [] [(a, _)] [] []) _ [] := h
      cases h'
      dsimp only
      have hlow : bv_unsigned a ≤ two_pow_64 - 4096 := by omega
      rw [errno_ret_in_below mmap_errnos a (by decide) hlow, ite_eq_right Bool.false_ne_true,
        ite_eq_left]
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨decide_eq_true h1, decide_eq_true h2⟩, decide_eq_true h3⟩, h4⟩,
        (listNN_eqb_eq _ _).mpr rfl⟩
  rw [ite_eq_right hp2] at h ⊢
  -- MAP_FIXED with PROT_NONE
  by_cases hp3 : mmap_fixed_noaccess_b prot flags off = true
  · rw [ite_eq_left hp3] at h ⊢
    by_cases hg : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals simp only [err_ret, ret_only, Monad.pure, unmodeled, reduceCtorEq] at h
      all_goals cases h; exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    rw [ite_eq_right hg] at h ⊢
    have h := (bind_get_model_iff _ i m _).mp h
    by_cases hc : (!decide (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
        ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc] at h ⊢
      have h' : Ok eff m' evs = Unmodeled := h
      cases h'
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h ⊢
      have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
      cases h'
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz] at h
      have h' : Ok eff m' evs = Unmodeled := h
      cases h'
    rw [ite_eq_right hz] at h ⊢
    have hc' := of_not_gate hc
    have hlow : bv_unsigned addr ≤ two_pow_64 - 4096 := by omega
    have he0 := errno_ret_in_below mmap_errnos addr (by decide) hlow
    by_cases hk : (region_free (m_vmmaps m).vm_reserved addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        && map_contains (m_vmmaps m).vm_maps addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) = true
    · -- contained
      rw [ite_eq_left hk] at h ⊢
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, hin, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [] [] []) m [] := he
        cases he'
        dsimp only
        rw [ite_eq_left (errno_ret_in_intro _ _ hin)]
      rcases (alt_iff _ _ i m _).mp h with h | h
      · have h := (bind_modify_iff _ _ i m _).mp h
        have h' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU addr [] [] [(addr, _)] [] []) _ [] := h
        cases h'
        dsimp only
        rw [he0, ite_eq_right Bool.false_ne_true, ite_eq_left]
        rw [Bool.and_eq_true]
        exact ⟨bv_eqb_refl _, (listNN_eqb_eq _ _).mpr rfl⟩
      · obtain ⟨e, hin, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [(addr, _)] [] []) _ [] := h
        cases h'
        dsimp only
        rw [ite_eq_left (errno_ret_in_intro _ _ hin), ite_eq_left ((listNN_eqb_eq _ _).mpr rfl)]
    rw [ite_eq_right hk] at h ⊢
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- free range
      rw [ite_eq_left hf] at h ⊢
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, hin, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [] [] []) m [] := he
        cases he'
        dsimp only
        rw [ite_eq_left (errno_ret_in_intro _ _ hin)]
      · obtain ⟨a, haa, h⟩ := (bind_choose_iff _ _ i m _).mp h
        rw [haa] at h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU addr [] [] [(addr, _)] [] []) _ [] := h
        cases h'
        dsimp only
        rw [he0, ite_eq_right Bool.false_ne_true, ite_eq_left]
        rw [Bool.and_eq_true]
        exact ⟨bv_eqb_refl _, (listNN_eqb_eq _ _).mpr rfl⟩
    rw [ite_eq_right hf] at h ⊢
    by_cases hs : region_free (m_vmmaps m).vm_reserved addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- spanning
      rw [ite_eq_left hs] at h ⊢
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, hin, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [] [] []) m [] := he
        cases he'
        dsimp only
        rw [ite_eq_left (errno_ret_in_intro _ _ hin)]
      rcases (alt_iff _ _ i m _).mp h with h | h
      · have h := (bind_modify_iff _ _ i m _).mp h
        have h' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU addr [] [] [(addr, _)] [] []) _ [] := h
        cases h'
        dsimp only
        rw [he0, ite_eq_right Bool.false_ne_true, ite_eq_left]
        rw [Bool.and_eq_true]
        exact ⟨bv_eqb_refl _, (listNN_eqb_eq _ _).mpr rfl⟩
      · obtain ⟨e, hin, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [(addr, _)] [] []) _ [] := h
        cases h'
        dsimp only
        rw [ite_eq_left (errno_ret_in_intro _ _ hin), ite_eq_left ((listNN_eqb_eq _ _).mpr rfl)]
    rw [ite_eq_right hs] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  rw [ite_eq_right hp3] at h ⊢
  -- MAP_FIXED with rw
  by_cases hp4 : mmap_fixed_rw_b prot flags off = true
  · rw [ite_eq_left hp4] at h ⊢
    by_cases hg : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals simp only [err_ret, ret_only, Monad.pure, unmodeled, reduceCtorEq] at h
      all_goals cases h; exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    rw [ite_eq_right hg] at h ⊢
    have h := (bind_get_model_iff _ i m _).mp h
    by_cases hc : (!decide (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
        ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc] at h ⊢
      have h' : Ok eff m' evs = Unmodeled := h
      cases h'
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h ⊢
      have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
      cases h'
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz] at h
      have h' : Ok eff m' evs = Unmodeled := h
      cases h'
    rw [ite_eq_right hz] at h ⊢
    have hc' := of_not_gate hc
    have hlow : bv_unsigned addr ≤ two_pow_64 - 4096 := by omega
    have he0 := errno_ret_in_below mmap_errnos addr (by decide) hlow
    by_cases hk : (region_free (m_vmmaps m).vm_reserved addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        && map_contains (m_vmmaps m).vm_maps addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) = true
    · -- contained
      rw [ite_eq_left hk] at h ⊢
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, hin, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [] [] []) m [] := he
        cases he'
        dsimp only
        rw [ite_eq_left (errno_ret_in_intro _ _ hin)]
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨_, hbud, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU addr [] [(addr, _)] [] [] []) _ [] := h
        cases h'
        dsimp only
        rw [he0, ite_eq_right Bool.false_ne_true, ite_eq_left]
        rw [Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨bv_eqb_refl _, (listNN_eqb_eq _ _).mpr rfl⟩, hbud⟩
      · obtain ⟨e, hin, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [(addr, _)] [] []) _ [] := h
        cases h'
        dsimp only
        rw [ite_eq_left (errno_ret_in_intro _ _ hin), ite_eq_left ((listNN_eqb_eq _ _).mpr rfl)]
    rw [ite_eq_right hk] at h ⊢
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- free range
      rw [ite_eq_left hf] at h ⊢
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, hin, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [] [] []) m [] := he
        cases he'
        dsimp only
        rw [ite_eq_left (errno_ret_in_intro _ _ hin)]
      · obtain ⟨a, ⟨haa, hbud⟩, h⟩ := (bind_choose_iff _ _ i m _).mp h
        rw [haa] at h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU addr [] [(addr, _)] [] [] []) _ [] := h
        cases h'
        dsimp only
        rw [he0, ite_eq_right Bool.false_ne_true, ite_eq_left]
        rw [Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨bv_eqb_refl _, (listNN_eqb_eq _ _).mpr rfl⟩, hbud⟩
    rw [ite_eq_right hf] at h ⊢
    by_cases hs : region_free (m_vmmaps m).vm_reserved addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- spanning
      rw [ite_eq_left hs] at h ⊢
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, hin, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [] [] []) m [] := he
        cases he'
        dsimp only
        rw [ite_eq_left (errno_ret_in_intro _ _ hin)]
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨_, hbud, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU addr [] [(addr, _)] [] [] []) _ [] := h
        cases h'
        dsimp only
        rw [he0, ite_eq_right Bool.false_ne_true, ite_eq_left]
        rw [Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨bv_eqb_refl _, (listNN_eqb_eq _ _).mpr rfl⟩, hbud⟩
      · obtain ⟨e, hin, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [(addr, _)] [] []) _ [] := h
        cases h'
        dsimp only
        rw [ite_eq_left (errno_ret_in_intro _ _ hin), ite_eq_left ((listNN_eqb_eq _ _).mpr rfl)]
    rw [ite_eq_right hs] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  rw [ite_eq_right hp4] at h ⊢
  -- MAP_FIXED_NOREPLACE with PROT_NONE
  by_cases hp5 : mmap_noreplace_noaccess_b prot flags off = true
  · rw [ite_eq_left hp5] at h ⊢
    by_cases hg : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals simp only [err_ret, ret_only, Monad.pure, unmodeled, reduceCtorEq] at h
      all_goals cases h; exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    rw [ite_eq_right hg] at h ⊢
    have h := (bind_get_model_iff _ i m _).mp h
    by_cases hc : (!decide (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
        ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc] at h ⊢
      have h' : Ok eff m' evs = Unmodeled := h
      cases h'
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h ⊢
      have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
      cases h'
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz] at h
      have h' : Ok eff m' evs = Unmodeled := h
      cases h'
    rw [ite_eq_right hz] at h ⊢
    have hc' := of_not_gate hc
    have hlow : bv_unsigned addr ≤ two_pow_64 - 4096 := by omega
    have he0 := errno_ret_in_below mmap_errnos addr (by decide) hlow
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- free range
      rw [ite_eq_left hf] at h ⊢
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, hin, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [] [] []) m [] := he
        cases he'
        dsimp only
        rw [ite_eq_left (errno_ret_in_intro _ _ hin)]
      · obtain ⟨a, haa, h⟩ := (bind_choose_iff _ _ i m _).mp h
        rw [haa] at h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU addr [] [] [(addr, _)] [] []) _ [] := h
        cases h'
        dsimp only
        rw [he0, ite_eq_right Bool.false_ne_true, ite_eq_left]
        rw [Bool.and_eq_true]
        exact ⟨bv_eqb_refl _, (listNN_eqb_eq _ _).mpr rfl⟩
    -- occupied: the environment errno or -EEXIST
    rw [ite_eq_right hf] at h ⊢
    rcases (alt_iff _ _ i m _).mp h with h | h
    · obtain ⟨e, hin, he⟩ := (bind_choose_iff _ _ i m _).mp h
      have he' : Ok eff m' evs
          = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [] [] []) m [] := he
      cases he'
      dsimp only
      rw [ite_eq_left (by rw [errno_ret_in_intro _ _ hin, Bool.true_or])]
    · have h' : Ok eff m' evs
          = Ok (SyscallEffect.mkEffectU (errno_ret EEXIST) [] [] [] [] []) m [] := h
      cases h'
      dsimp only
      rw [ite_eq_left (by rw [bv_eqb_refl, Bool.or_true])]
  rw [ite_eq_right hp5] at h ⊢
  -- MAP_FIXED_NOREPLACE with rw
  by_cases hp6 : mmap_noreplace_rw_b prot flags off = true
  · rw [ite_eq_left hp6] at h ⊢
    by_cases hg : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals simp only [err_ret, ret_only, Monad.pure, unmodeled, reduceCtorEq] at h
      all_goals cases h; exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    rw [ite_eq_right hg] at h ⊢
    have h := (bind_get_model_iff _ i m _).mp h
    by_cases hc : (!decide (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
        ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc] at h ⊢
      have h' : Ok eff m' evs = Unmodeled := h
      cases h'
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h ⊢
      have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
      cases h'
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz] at h
      have h' : Ok eff m' evs = Unmodeled := h
      cases h'
    rw [ite_eq_right hz] at h ⊢
    have hc' := of_not_gate hc
    have hlow : bv_unsigned addr ≤ two_pow_64 - 4096 := by omega
    have he0 := errno_ret_in_below mmap_errnos addr (by decide) hlow
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- free range
      rw [ite_eq_left hf] at h ⊢
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, hin, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [] [] []) m [] := he
        cases he'
        dsimp only
        rw [ite_eq_left (errno_ret_in_intro _ _ hin)]
      · obtain ⟨a, ⟨haa, hbud⟩, h⟩ := (bind_choose_iff _ _ i m _).mp h
        rw [haa] at h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU addr [] [(addr, _)] [] [] []) _ [] := h
        cases h'
        dsimp only
        rw [he0, ite_eq_right Bool.false_ne_true, ite_eq_left]
        rw [Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨bv_eqb_refl _, (listNN_eqb_eq _ _).mpr rfl⟩, hbud⟩
    -- occupied: the environment errno or -EEXIST
    rw [ite_eq_right hf] at h ⊢
    rcases (alt_iff _ _ i m _).mp h with h | h
    · obtain ⟨e, hin, he⟩ := (bind_choose_iff _ _ i m _).mp h
      have he' : Ok eff m' evs
          = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [] [] []) m [] := he
      cases he'
      dsimp only
      rw [ite_eq_left (by rw [errno_ret_in_intro _ _ hin, Bool.true_or])]
    · have h' : Ok eff m' evs
          = Ok (SyscallEffect.mkEffectU (errno_ret EEXIST) [] [] [] [] []) m [] := h
      cases h'
      dsimp only
      rw [ite_eq_left (by rw [bv_eqb_refl, Bool.or_true])]
  rw [ite_eq_right hp6] at h
  have h' : Ok eff m' evs = Unmodeled := h
  cases h'

/-- Every run the spec leaves unmodeled is one the checker declines,
whatever effect it is shown.  Rocq: `check_mmap_complete_unmodeled`. -/
theorem check_mmap_complete_unmodeled (addr len prot flags fd off : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (h : mmap_spec addr len prot flags fd off i m Unmodeled) :
    check_mmap addr len prot flags fd off eff m = CheckUnmodeled := by
  unfold mmap_spec at h
  unfold check_mmap
  dsimp only at h
  dsimp only
  by_cases hg1 : (!mmap_off_aligned_b off) = true
  · rw [ite_eq_left hg1] at h ⊢
    cases hp : mmap_pglen_ok_b len
    · rw [ite_eq_right Bool.false_ne_true]
    · rw [hp, ite_eq_left rfl] at h
      have h' : (Unmodeled : outcome SyscallEffect)
          = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
      cases h'
  rw [ite_eq_right hg1] at h ⊢
  by_cases hg2 : (!mmap_anon_b flags) = true
  · rw [ite_eq_left hg2]
  rw [ite_eq_right hg2] at h ⊢
  by_cases hg3 : w_is0 len = true
  · rw [ite_eq_left hg3] at h ⊢
    cases hp : mmap_plain_anon_b flags
    · rw [ite_eq_right Bool.false_ne_true]
    · rw [hp, ite_eq_left rfl] at h
      have h' : (Unmodeled : outcome SyscallEffect)
          = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
      cases h'
  rw [ite_eq_right hg3] at h ⊢
  -- the two placement arms are never unmodeled past their gate
  by_cases hp1 : mmap_modeled_b prot flags off = true
  · rw [ite_eq_left hp1] at h
    exfalso
    rcases (alt_iff _ _ i m _).mp h with h | h
    · obtain ⟨e, _, he⟩ := (bind_choose_iff _ _ i m _).mp h
      have he' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := he
      cases he'
    · have h := (bind_get_model_iff _ i m _).mp h
      obtain ⟨a, _, h⟩ := (bind_choose_iff _ _ i m _).mp h
      have h := (bind_modify_iff _ _ i m _).mp h
      have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
      cases h'
  rw [ite_eq_right hp1] at h ⊢
  by_cases hp2 : mmap_noaccess_b prot flags off = true
  · rw [ite_eq_left hp2] at h
    exfalso
    rcases (alt_iff _ _ i m _).mp h with h | h
    · obtain ⟨e, _, he⟩ := (bind_choose_iff _ _ i m _).mp h
      have he' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := he
      cases he'
    · have h := (bind_get_model_iff _ i m _).mp h
      obtain ⟨a, _, h⟩ := (bind_choose_iff _ _ i m _).mp h
      have h := (bind_modify_iff _ _ i m _).mp h
      have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
      cases h'
  rw [ite_eq_right hp2] at h ⊢
  -- MAP_FIXED with PROT_NONE
  by_cases hp3 : mmap_fixed_noaccess_b prot flags off = true
  · rw [ite_eq_left hp3] at h ⊢
    by_cases hg : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals first | rfl | simp only [err_ret, ret_only, Monad.pure, reduceCtorEq] at h
    rw [ite_eq_right hg] at h ⊢
    have h := (bind_get_model_iff _ i m _).mp h
    by_cases hc : (!decide (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
        ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc]
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h
      have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
      cases h'
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz]
    rw [ite_eq_right hz] at h ⊢
    by_cases hk : (region_free (m_vmmaps m).vm_reserved addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        && map_contains (m_vmmaps m).vm_maps addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) = true
    · rw [ite_eq_left hk] at h
      exfalso
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, _, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := he
        cases he'
      rcases (alt_iff _ _ i m _).mp h with h | h
      · have h := (bind_modify_iff _ _ i m _).mp h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
        cases h'
      · obtain ⟨e, _, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
        cases h'
    rw [ite_eq_right hk] at h ⊢
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hf] at h
      exfalso
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, _, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := he
        cases he'
      · obtain ⟨a, _, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
        cases h'
    rw [ite_eq_right hf] at h ⊢
    by_cases hs : region_free (m_vmmaps m).vm_reserved addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hs] at h
      exfalso
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, _, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := he
        cases he'
      rcases (alt_iff _ _ i m _).mp h with h | h
      · have h := (bind_modify_iff _ _ i m _).mp h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
        cases h'
      · obtain ⟨e, _, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
        cases h'
    rw [ite_eq_right hs]
  rw [ite_eq_right hp3] at h ⊢
  -- MAP_FIXED with rw
  by_cases hp4 : mmap_fixed_rw_b prot flags off = true
  · rw [ite_eq_left hp4] at h ⊢
    by_cases hg : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals first | rfl | simp only [err_ret, ret_only, Monad.pure, reduceCtorEq] at h
    rw [ite_eq_right hg] at h ⊢
    have h := (bind_get_model_iff _ i m _).mp h
    by_cases hc : (!decide (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
        ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc]
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h
      have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
      cases h'
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz]
    rw [ite_eq_right hz] at h ⊢
    by_cases hk : (region_free (m_vmmaps m).vm_reserved addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        && map_contains (m_vmmaps m).vm_maps addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) = true
    · rw [ite_eq_left hk] at h
      exfalso
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, _, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := he
        cases he'
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨_, _, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
        cases h'
      · obtain ⟨e, _, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
        cases h'
    rw [ite_eq_right hk] at h ⊢
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hf] at h
      exfalso
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, _, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := he
        cases he'
      · obtain ⟨a, _, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
        cases h'
    rw [ite_eq_right hf] at h ⊢
    by_cases hs : region_free (m_vmmaps m).vm_reserved addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hs] at h
      exfalso
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, _, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := he
        cases he'
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨_, _, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
        cases h'
      · obtain ⟨e, _, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
        cases h'
    rw [ite_eq_right hs]
  rw [ite_eq_right hp4] at h ⊢
  -- MAP_FIXED_NOREPLACE, either prot: past the gate both ledger sub-cases answer
  by_cases hp5 : mmap_noreplace_noaccess_b prot flags off = true
  · rw [ite_eq_left hp5] at h ⊢
    by_cases hg : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals first | rfl | simp only [err_ret, ret_only, Monad.pure, reduceCtorEq] at h
    rw [ite_eq_right hg] at h ⊢
    have h := (bind_get_model_iff _ i m _).mp h
    by_cases hc : (!decide (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
        ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc]
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h
      have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
      cases h'
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz]
    rw [ite_eq_right hz] at h
    exfalso
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hf] at h
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, _, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := he
        cases he'
      · obtain ⟨a, _, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
        cases h'
    rw [ite_eq_right hf] at h
    rcases (alt_iff _ _ i m _).mp h with h | h
    · obtain ⟨e, _, he⟩ := (bind_choose_iff _ _ i m _).mp h
      have he' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := he
      cases he'
    · have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
      cases h'
  rw [ite_eq_right hp5] at h ⊢
  by_cases hp6 : mmap_noreplace_rw_b prot flags off = true
  · rw [ite_eq_left hp6] at h ⊢
    by_cases hg : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · rw [ite_eq_left hg] at h ⊢
      generalize page_round_up_Z (bv_unsigned len) = N at h ⊢
      generalize bv_unsigned addr = A at h ⊢
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h ⊢
      all_goals first | rfl | simp only [err_ret, ret_only, Monad.pure, reduceCtorEq] at h
    rw [ite_eq_right hg] at h ⊢
    have h := (bind_get_model_iff _ i m _).mp h
    by_cases hc : (!decide (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
        ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc]
    rw [ite_eq_right hc] at h ⊢
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h
      have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
      cases h'
    rw [ite_eq_right ha] at h ⊢
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz]
    rw [ite_eq_right hz] at h
    exfalso
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hf] at h
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, _, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := he
        cases he'
      · obtain ⟨a, _, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
        cases h'
    rw [ite_eq_right hf] at h
    rcases (alt_iff _ _ i m _).mp h with h | h
    · obtain ⟨e, _, he⟩ := (bind_choose_iff _ _ i m _).mp h
      have he' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := he
      cases he'
    · have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
      cases h'
  rw [ite_eq_right hp6]

/-! ## The witness

One admissible outcome per input, for progress.  Rocq: `mmap_witness`
in `Checks/Witness/Mm/Mmap.v`.  Where a gate fixes the answer the
witness gives that answer; everywhere else it takes the errno arm,
because `errno_from mmap_errnos` is admitted whatever the ledger holds —
no placement has to be found and no budget consulted — and
`witness_errno` heads that list.  The MAP_FIXED shapes allow three
resolutions; the witness keeps choosing the errno one that leaves the
range in place, since it only has to be AN admissible outcome.  Declines
are exactly the checker's. -/

set_option linter.unusedVariables false in
/-- The mmap witness.  `fd` is unread, as `mmap_spec` never reads it on
the anonymous arm (`ksys_mmap_pgoff`, mm/mmap.c, Linux v6.18.46 at
1f99e9ab748f, resolves a file only inside `if (!(flags & MAP_ANONYMOUS))`). -/
def mmap_witness (addr len prot flags fd off : word) (m : Model) : outcome SyscallEffect :=
  if !(mmap_off_aligned_b off) then
    (if mmap_pglen_ok_b len then ret_outcome (errno_ret EINVAL) m else Unmodeled)
  else if !(mmap_anon_b flags) then Unmodeled
  else if w_is0 len then
    (if mmap_plain_anon_b flags then ret_outcome (errno_ret EINVAL) m else Unmodeled)
  else if mmap_modeled_b prot flags off then ret_outcome (errno_ret witness_errno) m
  else if mmap_noaccess_b prot flags off then ret_outcome (errno_ret witness_errno) m
  else if mmap_fixed_noaccess_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len)
    if two_pow_64 ≤ bv_unsigned addr + nZ then
      if two_pow_64 ≤ nZ then ret_outcome (errno_ret ENOMEM) m
      else if two_pow_64 - page_size < bv_unsigned addr then
        Unmodeled
      else if bv_unsigned addr % page_size = 0 then
        if bv_unsigned addr + nZ = two_pow_64 then
          Unmodeled
        else ret_outcome (errno_ret ENOMEM) m
      else
        Unmodeled
    else if !(bv_unsigned addr + nZ ≤ alloc_top (m_vmmaps m)) then Unmodeled
    else if !(bv_unsigned addr % page_size == 0) then ret_outcome (errno_ret EINVAL) m
    else if !(0 < bv_unsigned addr) then Unmodeled
    else
      let n := Z_to_bv 64 nZ
      if region_free (m_vmmaps m).vm_reserved addr n && map_contains (m_vmmaps m).vm_maps addr n
      then ret_outcome (errno_ret witness_errno) m
      else if region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr n
      then ret_outcome (errno_ret witness_errno) m
      else if region_free (m_vmmaps m).vm_reserved addr n
      then ret_outcome (errno_ret witness_errno) m
      else Unmodeled
  else if mmap_fixed_rw_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len)
    if two_pow_64 ≤ bv_unsigned addr + nZ then
      if two_pow_64 ≤ nZ then ret_outcome (errno_ret ENOMEM) m
      else if two_pow_64 - page_size < bv_unsigned addr then
        Unmodeled
      else if bv_unsigned addr % page_size = 0 then
        if bv_unsigned addr + nZ = two_pow_64 then
          Unmodeled
        else ret_outcome (errno_ret ENOMEM) m
      else
        Unmodeled
    else if !(bv_unsigned addr + nZ ≤ alloc_top (m_vmmaps m)) then Unmodeled
    else if !(bv_unsigned addr % page_size == 0) then ret_outcome (errno_ret EINVAL) m
    else if !(0 < bv_unsigned addr) then Unmodeled
    else
      let n := Z_to_bv 64 nZ
      if region_free (m_vmmaps m).vm_reserved addr n && map_contains (m_vmmaps m).vm_maps addr n
      then ret_outcome (errno_ret witness_errno) m
      else if region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr n
      then ret_outcome (errno_ret witness_errno) m
      else if region_free (m_vmmaps m).vm_reserved addr n
      then ret_outcome (errno_ret witness_errno) m
      else Unmodeled
  -- MAP_FIXED_NOREPLACE, either prot: past the MAP_FIXED argument gate BOTH
  -- ledger sub-cases carry the errno arm — the free range as an ordinary
  -- grant, the occupied one beside its -EEXIST — so no ledger test
  else if mmap_noreplace_noaccess_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len)
    if two_pow_64 ≤ bv_unsigned addr + nZ then
      if two_pow_64 ≤ nZ then ret_outcome (errno_ret ENOMEM) m
      else if two_pow_64 - page_size < bv_unsigned addr then
        Unmodeled
      else if bv_unsigned addr % page_size = 0 then
        if bv_unsigned addr + nZ = two_pow_64 then
          Unmodeled
        else ret_outcome (errno_ret ENOMEM) m
      else
        Unmodeled
    else if !(bv_unsigned addr + nZ ≤ alloc_top (m_vmmaps m)) then Unmodeled
    else if !(bv_unsigned addr % page_size == 0) then ret_outcome (errno_ret EINVAL) m
    else if !(0 < bv_unsigned addr) then Unmodeled
    else ret_outcome (errno_ret witness_errno) m
  else if mmap_noreplace_rw_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len)
    if two_pow_64 ≤ bv_unsigned addr + nZ then
      if two_pow_64 ≤ nZ then ret_outcome (errno_ret ENOMEM) m
      else if two_pow_64 - page_size < bv_unsigned addr then
        Unmodeled
      else if bv_unsigned addr % page_size = 0 then
        if bv_unsigned addr + nZ = two_pow_64 then
          Unmodeled
        else ret_outcome (errno_ret ENOMEM) m
      else
        Unmodeled
    else if !(bv_unsigned addr + nZ ≤ alloc_top (m_vmmaps m)) then Unmodeled
    else if !(bv_unsigned addr % page_size == 0) then ret_outcome (errno_ret EINVAL) m
    else if !(0 < bv_unsigned addr) then Unmodeled
    else ret_outcome (errno_ret witness_errno) m
  else Unmodeled

/-- The witness is admitted by the spec.  Rocq: `mmap_witness_ok`. -/
theorem mmap_witness_ok (addr len prot flags fd off : word) (i : SyscallInput) (m : Model) :
    mmap_spec addr len prot flags fd off i m (mmap_witness addr len prot flags fd off m) := by
  unfold mmap_spec mmap_witness
  dsimp only
  generalize bv_unsigned addr + page_round_up_Z (bv_unsigned len) = X
  by_cases hg1 : (!mmap_off_aligned_b off) = true
  · rw [ite_eq_left hg1, ite_eq_left hg1]
    cases hp : mmap_pglen_ok_b len
    · rw [ite_eq_right Bool.false_ne_true]
      exact unmodeled_intro i m
    · rw [ite_eq_left rfl]
      exact pure_ok _ i m
  rw [ite_eq_right hg1, ite_eq_right hg1]
  by_cases hg2 : (!mmap_anon_b flags) = true
  · rw [ite_eq_left hg2, ite_eq_left hg2]
    exact unmodeled_intro i m
  rw [ite_eq_right hg2, ite_eq_right hg2]
  by_cases hg3 : w_is0 len = true
  · rw [ite_eq_left hg3, ite_eq_left hg3]
    cases hp : mmap_plain_anon_b flags
    · rw [ite_eq_right Bool.false_ne_true]
      exact unmodeled_intro i m
    · rw [ite_eq_left rfl]
      exact pure_ok _ i m
  rw [ite_eq_right hg3, ite_eq_right hg3]
  by_cases hp1 : mmap_modeled_b prot flags off = true
  · rw [ite_eq_left hp1, ite_eq_left hp1]
    apply alt_l
    apply bind_step _ _ i m ENOMEM m _ (errno_head_witness _ _ i m)
    exact pure_ok _ i m
  rw [ite_eq_right hp1, ite_eq_right hp1]
  by_cases hp2 : mmap_noaccess_b prot flags off = true
  · rw [ite_eq_left hp2, ite_eq_left hp2]
    apply alt_l
    apply bind_step _ _ i m ENOMEM m _ (errno_head_witness _ _ i m)
    exact pure_ok _ i m
  rw [ite_eq_right hp2, ite_eq_right hp2]
  by_cases hp3 : mmap_fixed_noaccess_b prot flags off = true
  · rw [ite_eq_left hp3, ite_eq_left hp3]
    by_cases hg : two_pow_64 ≤ X
    · rw [ite_eq_left hg, ite_eq_left hg]
      generalize page_round_up_Z (bv_unsigned len) = N
      generalize bv_unsigned addr = A
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : X = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte]
      all_goals first | exact pure_ok _ i m | exact unmodeled_intro i m
    rw [ite_eq_right hg, ite_eq_right hg]
    apply bind_step _ _ i m m m _ (get_model_ok i m)
    by_cases hc : (!decide (X ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc, ite_eq_left hc]
      exact unmodeled_intro i m
    rw [ite_eq_right hc, ite_eq_right hc]
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha, ite_eq_left ha]
      exact pure_ok _ i m
    rw [ite_eq_right ha, ite_eq_right ha]
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz, ite_eq_left hz]
      exact unmodeled_intro i m
    rw [ite_eq_right hz, ite_eq_right hz]
    by_cases hk : (region_free (m_vmmaps m).vm_reserved addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        && map_contains (m_vmmaps m).vm_maps addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) = true
    · rw [ite_eq_left hk, ite_eq_left hk]
      apply alt_l
      apply bind_step _ _ i m ENOMEM m _ (errno_head_witness _ _ i m)
      exact pure_ok _ i m
    rw [ite_eq_right hk, ite_eq_right hk]
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hf, ite_eq_left hf]
      apply alt_l
      apply bind_step _ _ i m ENOMEM m _ (errno_head_witness _ _ i m)
      exact pure_ok _ i m
    rw [ite_eq_right hf, ite_eq_right hf]
    by_cases hs : region_free (m_vmmaps m).vm_reserved addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hs, ite_eq_left hs]
      apply alt_l
      apply bind_step _ _ i m ENOMEM m _ (errno_head_witness _ _ i m)
      exact pure_ok _ i m
    rw [ite_eq_right hs, ite_eq_right hs]
    exact unmodeled_intro i m
  rw [ite_eq_right hp3, ite_eq_right hp3]
  by_cases hp4 : mmap_fixed_rw_b prot flags off = true
  · rw [ite_eq_left hp4, ite_eq_left hp4]
    by_cases hg : two_pow_64 ≤ X
    · rw [ite_eq_left hg, ite_eq_left hg]
      generalize page_round_up_Z (bv_unsigned len) = N
      generalize bv_unsigned addr = A
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : X = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte]
      all_goals first | exact pure_ok _ i m | exact unmodeled_intro i m
    rw [ite_eq_right hg, ite_eq_right hg]
    apply bind_step _ _ i m m m _ (get_model_ok i m)
    by_cases hc : (!decide (X ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc, ite_eq_left hc]
      exact unmodeled_intro i m
    rw [ite_eq_right hc, ite_eq_right hc]
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha, ite_eq_left ha]
      exact pure_ok _ i m
    rw [ite_eq_right ha, ite_eq_right ha]
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz, ite_eq_left hz]
      exact unmodeled_intro i m
    rw [ite_eq_right hz, ite_eq_right hz]
    by_cases hk : (region_free (m_vmmaps m).vm_reserved addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        && map_contains (m_vmmaps m).vm_maps addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) = true
    · rw [ite_eq_left hk, ite_eq_left hk]
      apply alt_l
      apply bind_step _ _ i m ENOMEM m _ (errno_head_witness _ _ i m)
      exact pure_ok _ i m
    rw [ite_eq_right hk, ite_eq_right hk]
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hf, ite_eq_left hf]
      apply alt_l
      apply bind_step _ _ i m ENOMEM m _ (errno_head_witness _ _ i m)
      exact pure_ok _ i m
    rw [ite_eq_right hf, ite_eq_right hf]
    by_cases hs : region_free (m_vmmaps m).vm_reserved addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hs, ite_eq_left hs]
      apply alt_l
      apply bind_step _ _ i m ENOMEM m _ (errno_head_witness _ _ i m)
      exact pure_ok _ i m
    rw [ite_eq_right hs, ite_eq_right hs]
    exact unmodeled_intro i m
  rw [ite_eq_right hp4, ite_eq_right hp4]
  -- MAP_FIXED_NOREPLACE: the gate, then the errno arm of whichever `alt`
  -- the ledger selects.  Rocq proves both prot words with one Ltac,
  -- `mmap_noreplace_witness_step` (`Checks/Witness/Mm/Mmap.v`); the
  -- `hp5` and `hp6` blocks are that step written out once for each word,
  -- and stay identical while the two arms are.
  by_cases hp5 : mmap_noreplace_noaccess_b prot flags off = true
  · rw [ite_eq_left hp5, ite_eq_left hp5]
    by_cases hg : two_pow_64 ≤ X
    · rw [ite_eq_left hg, ite_eq_left hg]
      generalize page_round_up_Z (bv_unsigned len) = N
      generalize bv_unsigned addr = A
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : X = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte]
      all_goals first | exact pure_ok _ i m | exact unmodeled_intro i m
    rw [ite_eq_right hg, ite_eq_right hg]
    apply bind_step _ _ i m m m _ (get_model_ok i m)
    by_cases hc : (!decide (X ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc, ite_eq_left hc]
      exact unmodeled_intro i m
    rw [ite_eq_right hc, ite_eq_right hc]
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha, ite_eq_left ha]
      exact pure_ok _ i m
    rw [ite_eq_right ha, ite_eq_right ha]
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz, ite_eq_left hz]
      exact unmodeled_intro i m
    rw [ite_eq_right hz, ite_eq_right hz]
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hf]
      apply alt_l
      apply bind_step _ _ i m ENOMEM m _ (errno_head_witness _ _ i m)
      exact pure_ok _ i m
    rw [ite_eq_right hf]
    apply alt_l
    apply bind_step _ _ i m ENOMEM m _ (errno_head_witness _ _ i m)
    exact pure_ok _ i m
  rw [ite_eq_right hp5, ite_eq_right hp5]
  by_cases hp6 : mmap_noreplace_rw_b prot flags off = true
  · rw [ite_eq_left hp6, ite_eq_left hp6]
    by_cases hg : two_pow_64 ≤ X
    · rw [ite_eq_left hg, ite_eq_left hg]
      generalize page_round_up_Z (bv_unsigned len) = N
      generalize bv_unsigned addr = A
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : X = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte]
      all_goals first | exact pure_ok _ i m | exact unmodeled_intro i m
    rw [ite_eq_right hg, ite_eq_right hg]
    apply bind_step _ _ i m m m _ (get_model_ok i m)
    by_cases hc : (!decide (X ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc, ite_eq_left hc]
      exact unmodeled_intro i m
    rw [ite_eq_right hc, ite_eq_right hc]
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha, ite_eq_left ha]
      exact pure_ok _ i m
    rw [ite_eq_right ha, ite_eq_right ha]
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz, ite_eq_left hz]
      exact unmodeled_intro i m
    rw [ite_eq_right hz, ite_eq_right hz]
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · rw [ite_eq_left hf]
      apply alt_l
      apply bind_step _ _ i m ENOMEM m _ (errno_head_witness _ _ i m)
      exact pure_ok _ i m
    rw [ite_eq_right hf]
    apply alt_l
    apply bind_step _ _ i m ENOMEM m _ (errno_head_witness _ _ i m)
    exact pure_ok _ i m
  rw [ite_eq_right hp6, ite_eq_right hp6]
  exact unmodeled_intro i m

/-! ## The ledger is preserved

Rocq: `VmMapsDisjoint.check_mmap_preserves`.  Every accepted post-model
keeps `vm_maps` well-formed: the errno arms, the -EEXIST refusal and the
two `check_ret_only` answers hand the model back unchanged; the two
placement grants and the MAP_FIXED and MAP_FIXED_NOREPLACE free-range
grants cons a page-rounded, non-zero, free entry onto a well-formed list
(`maps_wf_cons_free`); the contained rw and
PROT_NONE replacements leave `vm_maps` untouched (`vmm_fixed_rw_next`
and the constructor's own projection); the destructive failure and the
two spanning grants go through `maps_subtract`, whose output is
well-formed (`maps_wf_subtract`) and free over the removed range
(`maps_subtract_region_free`).  The arithmetic side conditions all come
from the ceiling: a grant ending at or below `alloc_top` ends a stack's
width under `2^64` (`alloc_top_room`), so its page-rounded length
survives `Z_to_bv 64` (`u64`), and it is non-zero because `len` is
(`w_is0_false`, `page_round_up_pos`). -/

theorem check_mmap_preserves (addr len prot flags fd off : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_mmap addr len prot flags fd off eff m = CheckOk m' evs)
    (hwf : vm_wf (m_vmmaps m)) : vm_wf (m_vmmaps m') := by
  unfold check_mmap at h
  dsimp only at h
  have h64 : two_pow_64 = 18446744073709551616 := by decide
  have hroom := alloc_top_room (m_vmmaps m)
  unfold stack_max_size at hroom
  have haddr := word_range addr
  have hlen := word_range len
  by_cases hg1 : (!mmap_off_aligned_b off) = true
  · rw [ite_eq_left hg1] at h
    cases hp : mmap_pglen_ok_b len
    · rw [hp, ite_eq_right Bool.false_ne_true] at h
      cases h
    · rw [hp, ite_eq_left rfl] at h
      rw [check_ret_only_model h]
      exact hwf
  rw [ite_eq_right hg1] at h
  by_cases hg2 : (!mmap_anon_b flags) = true
  · rw [ite_eq_left hg2] at h
    cases h
  rw [ite_eq_right hg2] at h
  by_cases hg3 : w_is0 len = true
  · rw [ite_eq_left hg3] at h
    by_cases hp : mmap_plain_anon_b flags = true
    · rw [ite_eq_left hp] at h
      rw [check_ret_only_model h]
      exact hwf
    · rw [ite_eq_right hp] at h
      cases h
  rw [ite_eq_right hg3] at h
  have hlen0 : bv_unsigned len ≠ 0 := w_is0_false len (Bool.of_not_eq_true hg3)
  have hnpos : 0 < page_round_up_Z (bv_unsigned len) := page_round_up_pos _ (by omega)
  -- the plain rw grant
  by_cases hp1 : mmap_modeled_b prot flags off = true
  · rw [ite_eq_left hp1] at h
    split at h
    · rename_i r zs
      split at h
      · split at h
        · cases h
          exact hwf
        · cases h
      · split at h
        · rename_i hC
          simp only [Bool.and_eq_true, decide_eq_true_eq, listNN_eqb_eq] at hC
          obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, rfl⟩ := hC
          cases h
          have hr := word_range r
          unfold vm_wf
          rw [vmm_mmap_backing, m_vmmaps_with_vmmaps]
          apply maps_wf_cons_free _ _ _ hwf ?_ (region_free_app_r _ _ _ _ h4)
          rw [u64 _ (by omega) (by omega)]
          omega
        · cases h
    · cases h
  rw [ite_eq_right hp1] at h
  -- the plain PROT_NONE reservation
  by_cases hp2 : mmap_noaccess_b prot flags off = true
  · rw [ite_eq_left hp2] at h
    split at h
    · rename_i r us
      split at h
      · split at h
        · cases h
          exact hwf
        · cases h
      · split at h
        · rename_i hC
          simp only [Bool.and_eq_true, decide_eq_true_eq, listNN_eqb_eq] at hC
          obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, rfl⟩ := hC
          cases h
          have hr := word_range r
          unfold vm_wf
          rw [vmm_mmap_backing, m_vmmaps_with_vmmaps]
          apply maps_wf_cons_free _ _ _ hwf ?_ (region_free_app_r _ _ _ _ h4)
          rw [u64 _ (by omega) (by omega)]
          omega
        · cases h
    · cases h
  rw [ite_eq_right hp2] at h
  -- MAP_FIXED with PROT_NONE
  by_cases hp3 : mmap_fixed_noaccess_b prot flags off = true
  · rw [ite_eq_left hp3] at h
    by_cases hg : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · rw [ite_eq_left hg] at h
      generalize page_round_up_Z (bv_unsigned len) = N at h
      generalize bv_unsigned addr = A at h
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h
      all_goals first | cases h | rw [check_ret_only_model h]; exact hwf
    rw [ite_eq_right hg] at h
    by_cases hc : (!decide (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
        ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc] at h
      cases h
    rw [ite_eq_right hc] at h
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h
      rw [check_ret_only_model h]
      exact hwf
    rw [ite_eq_right ha] at h
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz] at h
      cases h
    rw [ite_eq_right hz] at h
    have hc' := of_not_gate hc
    have hz' := of_not_gate hz
    have hn : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        = page_round_up_Z (bv_unsigned len) := u64 _ (by omega) (by omega)
    by_cases hk : (region_free (m_vmmaps m).vm_reserved addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        && map_contains (m_vmmaps m).vm_maps addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) = true
    · -- contained: the replacement keeps `vm_maps`; the destroyed ledger subtracts the range
      rw [ite_eq_left hk] at h
      split at h
      · split at h
        · split at h
          · cases h
            exact hwf
          · split at h
            · cases h
              rw [vmm_mmap_destroyed]
              unfold vm_wf mmap_fixed_destroyed_next
              rw [hn]
              exact maps_wf_subtract _ _ _ (by omega) (by omega) (by omega) hwf
            · cases h
        · split at h
          · cases h
            unfold vm_wf
            rw [vmm_mmap_replacement, m_vmmaps_with_vmmaps]
            exact hwf
          · cases h
      · cases h
    rw [ite_eq_right hk] at h
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- free range: a fresh entry over a free range
      rw [ite_eq_left hf] at h
      split at h
      · split at h
        · split at h
          · cases h
            exact hwf
          · cases h
        · split at h
          · cases h
            unfold vm_wf
            rw [vmm_mmap_backing, m_vmmaps_with_vmmaps]
            apply maps_wf_cons_free _ _ _ hwf ?_ (region_free_app_r _ _ _ _ hf)
            rw [hn]
            omega
          · cases h
      · cases h
    rw [ite_eq_right hf] at h
    by_cases hs : region_free (m_vmmaps m).vm_reserved addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- spanning: the range re-cut, then the entry consed over the now-free range
      rw [ite_eq_left hs] at h
      split at h
      · split at h
        · split at h
          · cases h
            exact hwf
          · split at h
            · cases h
              rw [vmm_mmap_destroyed]
              unfold vm_wf mmap_fixed_destroyed_next
              rw [hn]
              exact maps_wf_subtract _ _ _ (by omega) (by omega) (by omega) hwf
            · cases h
        · split at h
          · cases h
            unfold vm_wf
            rw [vmm_mmap_replacement, m_vmmaps_with_vmmaps]
            unfold mmap_fixed_noaccess_span_next
            apply maps_wf_cons_free _ _ _ ?_ ?_ ?_
            · rw [hn]
              exact maps_wf_subtract _ _ _ (by omega) (by omega) (by omega) hwf
            · rw [hn]
              omega
            · exact maps_subtract_region_free _ _ _ (by rw [hn]; omega)
          · cases h
      · cases h
    rw [ite_eq_right hs] at h
    cases h
  rw [ite_eq_right hp3] at h
  -- MAP_FIXED with rw
  by_cases hp4 : mmap_fixed_rw_b prot flags off = true
  · rw [ite_eq_left hp4] at h
    by_cases hg : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · rw [ite_eq_left hg] at h
      generalize page_round_up_Z (bv_unsigned len) = N at h
      generalize bv_unsigned addr = A at h
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h
      all_goals first | cases h | rw [check_ret_only_model h]; exact hwf
    rw [ite_eq_right hg] at h
    by_cases hc : (!decide (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
        ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc] at h
      cases h
    rw [ite_eq_right hc] at h
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h
      rw [check_ret_only_model h]
      exact hwf
    rw [ite_eq_right ha] at h
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz] at h
      cases h
    rw [ite_eq_right hz] at h
    have hc' := of_not_gate hc
    have hz' := of_not_gate hz
    have hn : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        = page_round_up_Z (bv_unsigned len) := u64 _ (by omega) (by omega)
    by_cases hk : (region_free (m_vmmaps m).vm_reserved addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        && map_contains (m_vmmaps m).vm_maps addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) = true
    · -- contained
      rw [ite_eq_left hk] at h
      split at h
      · split at h
        · split at h
          · split at h
            · cases h
              exact hwf
            · split at h
              · cases h
                rw [vmm_mmap_destroyed]
                unfold vm_wf mmap_fixed_destroyed_next
                rw [hn]
                exact maps_wf_subtract _ _ _ (by omega) (by omega) (by omega) hwf
              · cases h
          · cases h
        · split at h
          · split at h
            · cases h
              unfold vm_wf
              rw [vmm_mmap_replacement, m_vmmaps_with_vmmaps, vmm_fixed_rw_next]
              exact hwf
            · cases h
          · cases h
      · cases h
    rw [ite_eq_right hk] at h
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- free range
      rw [ite_eq_left hf] at h
      split at h
      · split at h
        · split at h
          · cases h
            exact hwf
          · cases h
        · split at h
          · cases h
            unfold vm_wf
            rw [vmm_mmap_backing, m_vmmaps_with_vmmaps]
            apply maps_wf_cons_free _ _ _ hwf ?_ (region_free_app_r _ _ _ _ hf)
            rw [hn]
            omega
          · cases h
      · cases h
    rw [ite_eq_right hf] at h
    by_cases hs : region_free (m_vmmaps m).vm_reserved addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- spanning
      rw [ite_eq_left hs] at h
      split at h
      · split at h
        · split at h
          · split at h
            · cases h
              exact hwf
            · split at h
              · cases h
                rw [vmm_mmap_destroyed]
                unfold vm_wf mmap_fixed_destroyed_next
                rw [hn]
                exact maps_wf_subtract _ _ _ (by omega) (by omega) (by omega) hwf
              · cases h
          · cases h
        · split at h
          · split at h
            · cases h
              unfold vm_wf
              rw [vmm_mmap_replacement, m_vmmaps_with_vmmaps]
              unfold mmap_fixed_rw_span_next
              apply maps_wf_cons_free _ _ _ ?_ ?_ ?_
              · rw [hn]
                exact maps_wf_subtract _ _ _ (by omega) (by omega) (by omega) hwf
              · rw [hn]
                omega
              · exact maps_subtract_region_free _ _ _ (by rw [hn]; omega)
            · cases h
          · cases h
      · cases h
    rw [ite_eq_right hs] at h
    cases h
  rw [ite_eq_right hp4] at h
  -- MAP_FIXED_NOREPLACE with PROT_NONE
  by_cases hp5 : mmap_noreplace_noaccess_b prot flags off = true
  · rw [ite_eq_left hp5] at h
    by_cases hg : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · rw [ite_eq_left hg] at h
      generalize page_round_up_Z (bv_unsigned len) = N at h
      generalize bv_unsigned addr = A at h
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h
      all_goals first | cases h | rw [check_ret_only_model h]; exact hwf
    rw [ite_eq_right hg] at h
    by_cases hc : (!decide (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
        ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc] at h
      cases h
    rw [ite_eq_right hc] at h
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h
      rw [check_ret_only_model h]
      exact hwf
    rw [ite_eq_right ha] at h
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz] at h
      cases h
    rw [ite_eq_right hz] at h
    have hc' := of_not_gate hc
    have hn : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        = page_round_up_Z (bv_unsigned len) := u64 _ (by omega) (by omega)
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- free range: a fresh entry over a free range
      rw [ite_eq_left hf] at h
      split at h
      · split at h
        · split at h
          · cases h
            exact hwf
          · cases h
        · split at h
          · cases h
            unfold vm_wf
            rw [vmm_mmap_backing, m_vmmaps_with_vmmaps]
            apply maps_wf_cons_free _ _ _ hwf ?_ (region_free_app_r _ _ _ _ hf)
            rw [hn]
            omega
          · cases h
      · cases h
    -- occupied: the model is handed back
    rw [ite_eq_right hf] at h
    split at h
    · split at h
      · cases h
        exact hwf
      · cases h
    · cases h
  rw [ite_eq_right hp5] at h
  -- MAP_FIXED_NOREPLACE with rw
  by_cases hp6 : mmap_noreplace_rw_b prot flags off = true
  · rw [ite_eq_left hp6] at h
    by_cases hg : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · rw [ite_eq_left hg] at h
      generalize page_round_up_Z (bv_unsigned len) = N at h
      generalize bv_unsigned addr = A at h
      by_cases hlen : two_pow_64 ≤ N
      all_goals by_cases hband : two_pow_64 - page_size < A
      all_goals by_cases halign : A % page_size = 0
      all_goals by_cases hend : A + N = two_pow_64
      all_goals simp only [hlen, hband, halign, hend, ↓reduceIte] at h
      all_goals first | cases h | rw [check_ret_only_model h]; exact hwf
    rw [ite_eq_right hg] at h
    by_cases hc : (!decide (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
        ≤ alloc_top (m_vmmaps m))) = true
    · rw [ite_eq_left hc] at h
      cases h
    rw [ite_eq_right hc] at h
    by_cases ha : (!(bv_unsigned addr % page_size == 0)) = true
    · rw [ite_eq_left ha] at h
      rw [check_ret_only_model h]
      exact hwf
    rw [ite_eq_right ha] at h
    by_cases hz : (!decide (0 < bv_unsigned addr)) = true
    · rw [ite_eq_left hz] at h
      cases h
    rw [ite_eq_right hz] at h
    have hc' := of_not_gate hc
    have hn : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
        = page_round_up_Z (bv_unsigned len) := u64 _ (by omega) (by omega)
    by_cases hf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
    · -- free range: a fresh entry over a free range
      rw [ite_eq_left hf] at h
      split at h
      · split at h
        · split at h
          · cases h
            exact hwf
          · cases h
        · split at h
          · cases h
            unfold vm_wf
            rw [vmm_mmap_backing, m_vmmaps_with_vmmaps]
            apply maps_wf_cons_free _ _ _ hwf ?_ (region_free_app_r _ _ _ _ hf)
            rw [hn]
            omega
          · cases h
      · cases h
    -- occupied: the model is handed back
    rw [ite_eq_right hf] at h
    split at h
    · split at h
      · cases h
        exact hwf
      · cases h
    · cases h
  rw [ite_eq_right hp6] at h
  cases h

-- lean-port sentinel: ticket C-Mm-Mmap-brk-munmap appends below this line

/-! ## brk (214) and munmap (215) — C-Mm-Mmap-brk-munmap's half

Rocq: the first and third checkers of `Checks/Sys/Mm/Mmap.v` — `check_brk`
(:19, ahead of `check_mmap` at :31) and `check_munmap` (:358) — with the
four lemmas each, and the two witnesses of `Checks/Witness/Mm/Mmap.v`
with their `_ok` lemmas.  Read at the header's baseline.  THE BASELINE
above says `Checks/Sys/Mm/Mmap.v` is unchanged through 184fa7ead; so is
`Checks/Witness/Mm/Mmap.v`, blob `89f337d74371` at f44244ad, at a71fd38a
and at 184fa7ead, so nothing a checker or witness here was read from
differs between the brief's commit, the pin and the branch's base.

WHAT IS NOT HERE, AND WHOSE IT IS.  Rocq builds `arm_brk` and
`arm_munmap` and lists them in `checked_table` (`Checks/Sys/Dispatch.v`),
registers their `arm_unfold` equations, and proves `check_brk_preserves`
and `check_munmap_preserves` in `Checks/VmMapsDisjoint.v`.  In the Lean
port those are the registration step of the conformance ticket for the
two arms, not this ticket's (BRIEF.md section 5, the CHECK and VERIFY
blocks): the two checkers land on the preludes and the spec alone, and
the checked table's rows, the `arm_unfold` lemmas and the ledger's
per-arm alternatives are written when the arms are registered.  The mmap
half is shaped differently — `check_mmap_preserves` is stated below,
under the paragraph WHY THE PRESERVES LEMMA IS HERE — because K6b landed
as a `lean: base:` change carrying its own registration; the brk and
munmap halves follow the CHECK shape their ticket names, whose acceptance
lists no frame lemma, and the two halves are not made alike here.

HOW A CHECKER READS A SPEC THAT DRAWS.  `brk_spec` draws its answer with
`choose`, and a checker cannot draw: it is handed the guest's answer
inside `eff` and asks `brk_r_ok` whether the spec could have drawn it,
then recomputes the zero-fill and unmap lists from that answer and
compares them entry for entry.  The post-model is the spec's own
`with_brk_next` applied to the guest's answer, so an accepted `brk` is
never a state the spec could not have reached.  `munmap_spec` draws
nothing, so `check_munmap` walks the same `if`-chain arm for arm and the
only comparisons are `check_ret_only` and the one-entry unmap list.

WHAT THE PROOFS DO.  Each is a case split on the conditions the checker
branches on, in the order the spec tests them, with the spec's `bind`s
read through `Monad.lean`'s `bind_*_iff` lemmas, `bind_get_vmmaps_iff`
among them.  The Rocq proofs reach the same case split through
`sys_unfold`/`inv_ok`; the by-hand split is preferred here so that a
reader can line each Lean branch up with the checker arm it discharges.
It is a different shape from the mmap half's gate walk above because
neither spec zeta-binds a term both sides have to share: `munmap_spec`'s
`let`s are read by `simp only` in the same step as the `if` they feed.

THE WITNESSES.  `brk_witness` answers with the CURRENT break.  That answer
is admitted on every arm of `brk_r_ok`: it is the only answer where the
request is 0 or below `min_brk`, one of the two on a shrink, and on a
grow it is the failure branch, which `brk_grow_ok` never gates because a
break equal to itself is not a grow.  Linux does answer this way on every
refusal a task reads (`SYSCALL_DEFINE1(brk)`, mm/mmap.c:209-212, Linux
v6.18.46: `mm->brk = origbrk; ... return origbrk`): the -EINTR of
`mmap_write_lock_killable` (:125-126) is the exception the
brk header of `Sys/Mm/Mmap.lean` sets aside — it reaches only a task
SIGKILL is already killing — so the witness is a real answer and not a
convenient one.  `munmap_witness` has no choice to make:
`munmap_spec` draws nothing, and the witness is its `if`-chain with each
arm's single outcome written out, `Unmodeled` included. -/

/-! ### brk (214) -/

/-- The brk checker.  Rocq: `check_brk`.

Linux's `brk` (`SYSCALL_DEFINE1(brk)`, mm/mmap.c:115-213, Linux v6.18.46)
answers with the new break, or with the old one on every refusal a task
reads (`mm->brk = origbrk; ... return origbrk`, :209-212; the -EINTR of
:125-126 reaches only a task SIGKILL is already killing), and the spec's
`brk_r_ok` says which the answer `r` may be: either of the two on a
shrink, or on a grow the ledger can carry; the old break alone on a
query, on a request under `min_brk`, or on a grow it cannot carry.  The
checker takes `r` from the effect,
requires the zero-fill and unmap lists to be exactly the ones
`brk_zeros`/`brk_unmaps` derive from that `r` and the current break, and
moves the model by `with_brk_next`.  A write, a copyin or a memory copy in
the effect is refused before anything is compared: `brk` performs none. -/
def check_brk (req : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU r [] zs us [] [] =>
      if brk_r_ok m req r && listNN_eqb zs (brk_zeros req r (m_vmmaps m).vm_brk)
         && listNN_eqb us (brk_unmaps r (m_vmmaps m).vm_brk)
      then CheckOk (with_brk_next m req r) [] else CheckReject
  | _ => CheckReject

/-- Rocq: `check_brk_sound_ok`. -/
theorem check_brk_sound_ok (req : word) (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_brk req eff m = CheckOk m' evs) :
    brk_spec req i m (Ok eff m' evs) := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases cs <;> cases ci <;> simp only [check_brk, reduceCtorEq] at h
  by_cases hc : (brk_r_ok m req r && listNN_eqb zs (brk_zeros req r (m_vmmaps m).vm_brk)
      && listNN_eqb us (brk_unmaps r (m_vmmaps m).vm_brk)) = true
  · simp only [hc, ↓reduceIte, check_result.CheckOk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, listNN_eqb_eq] at hc
    obtain ⟨⟨hok, rfl⟩, rfl⟩ := hc
    simp only [brk_spec, bind_get_model_iff, bind_choose_iff, bind_modify_iff, pure_iff]
    exact ⟨r, hok, rfl⟩
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `check_brk_sound_unmodeled`.  Vacuous: no arm of `check_brk`
answers `CheckUnmodeled`, as no arm of `brk_spec` is `unmodeled`. -/
theorem check_brk_sound_unmodeled (req : word) (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (h : check_brk req eff m = CheckUnmodeled) : brk_spec req i m Unmodeled := by
  exfalso
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases cs <;> cases ci <;> simp only [check_brk, reduceCtorEq] at h
  by_cases hc : (brk_r_ok m req r && listNN_eqb zs (brk_zeros req r (m_vmmaps m).vm_brk)
      && listNN_eqb us (brk_unmaps r (m_vmmaps m).vm_brk)) = true
  · simp only [hc, ↓reduceIte, reduceCtorEq] at h
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `check_brk_complete_ok`. -/
theorem check_brk_complete_ok (req : word) (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : brk_spec req i m (Ok eff m' evs)) :
    check_brk req eff m = CheckOk m' evs := by
  simp only [brk_spec, bind_get_model_iff, bind_choose_iff, bind_modify_iff, pure_iff,
    outcome.Ok.injEq] at h
  obtain ⟨r, hok, rfl, rfl, rfl⟩ := h
  have hz := (listNN_eqb_eq (brk_zeros req r (m_vmmaps m).vm_brk) _).mpr rfl
  have hu := (listNN_eqb_eq (brk_unmaps r (m_vmmaps m).vm_brk) _).mpr rfl
  simp only [check_brk, hok, hz, hu, Bool.and_self, ↓reduceIte]

/-- Rocq: `check_brk_complete_unmodeled`.  Vacuous, as its soundness twin. -/
theorem check_brk_complete_unmodeled (req : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (h : brk_spec req i m Unmodeled) :
    check_brk req eff m = CheckUnmodeled := by
  exfalso
  simp only [brk_spec, bind_get_model_iff, bind_choose_iff, bind_modify_iff, pure_iff,
    reduceCtorEq, and_false, exists_false] at h

/-! ### The brk witness -/

/-- Rocq: `brk_witness`.  The unchanged break, with the zero and unmap
lists `brk_zeros`/`brk_unmaps` derive for a break that does not move —
both empty, though the definition says so by computing them rather than
by writing `[]`, so that the witness is the checker's accepting shape
by construction. -/
def brk_witness (req : word) (m : Model) : outcome SyscallEffect :=
  let h := m_vmmaps m
  let r := h.vm_brk
  Ok (SyscallEffect.mkEffectU r [] (brk_zeros req r h.vm_brk) (brk_unmaps r h.vm_brk) [] [])
     (with_brk_next m req r) []

/-- Rocq: `brk_witness_ok`. -/
theorem brk_witness_ok (req : word) (i : SyscallInput) (m : Model) :
    brk_spec req i m (brk_witness req m) := by
  simp only [brk_spec, brk_witness, bind_get_model_iff, bind_choose_iff, bind_modify_iff, pure_iff]
  refine ⟨(m_vmmaps m).vm_brk, ?_, rfl⟩
  have hb : bv_eqb (m_vmmaps m).vm_brk (m_vmmaps m).vm_brk = true := (bv_eqb_eq _ _).mpr rfl
  simp only [brk_r_ok, brk_grow_ok, hb, Bool.or_true, Bool.and_true, Int.lt_irrefl,
    decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ite_self]

/-! ### munmap (215) -/

/-- The munmap checker, in `munmap_spec`'s arm order.  Rocq: `check_munmap`.

`do_vmi_munmap` (mm/vma.c:1604-1627, Linux v6.18.46) refuses an unaligned
`start`, a `len` of 0 and a range past `TASK_SIZE` with -EINVAL before it
reads a VMA (:1611-1616), answers 0 when no VMA meets the range
(:1619-1623) and otherwise unmaps (:1626); the spec's header says how the
`Int` sum below is that gate.  The post-model of the exact-mapping arm is
what the spec's `set_vmmaps ;; forget_vm_range` builds, spelled out
because a checker cannot run the spec's `bind`; the decline sits where
the spec's does, after the ledger has been consulted and found neither
the exact mapping nor a free range under `alloc_top`. -/
def check_munmap (addr len : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if !(bv_unsigned addr % page_size == 0) || w_is0 len
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    let nZ := page_round_up_Z (bv_unsigned len)
    if TASK_SIZE < bv_unsigned addr + nZ then check_ret_only eff (errno_ret EINVAL) m []
    else
    let n := Z_to_bv 64 nZ
    if map_has (m_vmmaps m).vm_maps addr n then
      match eff with
      | SyscallEffect.mkEffectU r [] [] us [] [] =>
          if w_is0 r && listNN_eqb us [(addr, n)]
          then CheckOk (with_mmap_destroyed addr n
                 (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
                    (map_remove (m_vmmaps m).vm_maps addr)
                    (maps_subtract (m_vmmaps m).vm_noaccess (bv_unsigned addr)
                                   (bv_unsigned addr + bv_unsigned n))
                    (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit
                    (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp) m) []
          else CheckReject
      | _ => CheckReject
    else if munmap_free_ok (m_vmmaps m) addr nZ then check_ret_only eff (Z_to_bv 64 0) m []
    else CheckUnmodeled

/-- Rocq: `check_munmap_sound_ok`. -/
theorem check_munmap_sound_ok (addr len : word) (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_munmap addr len eff m = CheckOk m' evs) :
    munmap_spec addr len i m (Ok eff m' evs) := by
  by_cases h1 : (!(bv_unsigned addr % page_size == 0) || w_is0 len) = true
  · simp only [check_munmap, h1, ↓reduceIte] at h
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    simp only [munmap_spec, h1, ↓reduceIte, err_ret, ret_only, pure_iff]
  · by_cases h2 : TASK_SIZE < bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · simp only [check_munmap, h1, h2, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      simp only [munmap_spec, h1, h2, Bool.false_eq_true, ↓reduceIte, bind_get_vmmaps_iff,
        err_ret, ret_only, pure_iff]
    · by_cases h3 : map_has (m_vmmaps m).vm_maps addr
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
      · simp only [check_munmap, h1, h2, h3, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
        cases ws <;> cases zs <;> cases cs <;> cases ci <;> simp only [reduceCtorEq] at h
        by_cases hc : (w_is0 r
            && listNN_eqb us [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]) = true
        · simp only [hc, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Bool.and_eq_true, w_is0, bv_eqb_eq, listNN_eqb_eq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          simp only [munmap_spec, h1, h2, h3, Bool.false_eq_true, ↓reduceIte,
            bind_get_vmmaps_iff, set_vmmaps, forget_vm_range, bind_modify_iff, pure_iff,
            with_mmap_destroyed]
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      · by_cases h4 : munmap_free_ok (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)) = true
        · simp only [check_munmap, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
          simp only [munmap_spec, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte,
            bind_get_vmmaps_iff, ret_only, pure_iff]
        · simp only [check_munmap, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte,
            reduceCtorEq] at h

/-- Rocq: `check_munmap_sound_unmodeled`. -/
theorem check_munmap_sound_unmodeled (addr len : word) (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) (h : check_munmap addr len eff m = CheckUnmodeled) :
    munmap_spec addr len i m Unmodeled := by
  by_cases h1 : (!(bv_unsigned addr % page_size == 0) || w_is0 len) = true
  · simp only [check_munmap, h1, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  · by_cases h2 : TASK_SIZE < bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · simp only [check_munmap, h1, h2, Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    · by_cases h3 : map_has (m_vmmaps m).vm_maps addr
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
      · exfalso
        simp only [check_munmap, h1, h2, h3, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
        cases ws <;> cases zs <;> cases cs <;> cases ci <;> simp only [reduceCtorEq] at h
        by_cases hc : (w_is0 r
            && listNN_eqb us [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]) = true
        · simp only [hc, ↓reduceIte, reduceCtorEq] at h
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      · by_cases h4 : munmap_free_ok (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)) = true
        · simp only [check_munmap, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte] at h
          exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        · simp only [munmap_spec, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte,
            bind_get_vmmaps_iff, unmodeled_iff]

/-- Rocq: `check_munmap_complete_ok`. -/
theorem check_munmap_complete_ok (addr len : word) (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : munmap_spec addr len i m (Ok eff m' evs)) :
    check_munmap addr len eff m = CheckOk m' evs := by
  by_cases h1 : (!(bv_unsigned addr % page_size == 0) || w_is0 len) = true
  · simp only [munmap_spec, h1, ↓reduceIte, err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [check_munmap, h1, ↓reduceIte]
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · by_cases h2 : TASK_SIZE < bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · simp only [munmap_spec, h1, h2, Bool.false_eq_true, ↓reduceIte, bind_get_vmmaps_iff,
        err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [check_munmap, h1, h2, Bool.false_eq_true, ↓reduceIte]
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    · by_cases h3 : map_has (m_vmmaps m).vm_maps addr
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
      · simp only [munmap_spec, h1, h2, h3, Bool.false_eq_true, ↓reduceIte, bind_get_vmmaps_iff,
          set_vmmaps, forget_vm_range, bind_modify_iff, pure_iff, outcome.Ok.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hus := (listNN_eqb_eq
          [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] _).mpr rfl
        have hw : w_is0 (Z_to_bv 64 0) = true := bv_eqb_refl _
        simp only [check_munmap, h1, h2, h3, Bool.false_eq_true, ↓reduceIte, hw, hus,
          Bool.and_self, with_mmap_destroyed]
      · by_cases h4 : munmap_free_ok (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)) = true
        · simp only [munmap_spec, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte,
            bind_get_vmmaps_iff, ret_only, pure_iff, outcome.Ok.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp only [check_munmap, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
          exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
        · simp only [munmap_spec, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte,
            bind_get_vmmaps_iff, unmodeled_iff, reduceCtorEq] at h

/-- Rocq: `check_munmap_complete_unmodeled`. -/
theorem check_munmap_complete_unmodeled (addr len : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (h : munmap_spec addr len i m Unmodeled) :
    check_munmap addr len eff m = CheckUnmodeled := by
  by_cases h1 : (!(bv_unsigned addr % page_size == 0) || w_is0 len) = true
  · exfalso
    simp only [munmap_spec, h1, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h
  · by_cases h2 : TASK_SIZE < bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · exfalso
      simp only [munmap_spec, h1, h2, Bool.false_eq_true, ↓reduceIte, bind_get_vmmaps_iff,
        err_ret, ret_only, pure_iff, reduceCtorEq] at h
    · by_cases h3 : map_has (m_vmmaps m).vm_maps addr
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
      · exfalso
        simp only [munmap_spec, h1, h2, h3, Bool.false_eq_true, ↓reduceIte, bind_get_vmmaps_iff,
          set_vmmaps, forget_vm_range, bind_modify_iff, pure_iff, reduceCtorEq] at h
      · by_cases h4 : munmap_free_ok (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)) = true
        · exfalso
          simp only [munmap_spec, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte,
            bind_get_vmmaps_iff, ret_only, pure_iff, reduceCtorEq] at h
        · simp only [check_munmap, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]

/-! ### The munmap witness -/

/-- Rocq: `munmap_witness`.  The checker's `if`-chain with each arm's one
outcome: -EINVAL at the two gates, the exact teardown, the no-op 0, and
`Unmodeled` where the checker declines. -/
def munmap_witness (addr len : word) (m : Model) : outcome SyscallEffect :=
  if !(bv_unsigned addr % page_size == 0) || w_is0 len then ret_outcome (errno_ret EINVAL) m
  else
    let h := m_vmmaps m
    let nZ := page_round_up_Z (bv_unsigned len)
    if TASK_SIZE < bv_unsigned addr + nZ then ret_outcome (errno_ret EINVAL) m
    else
    let n := Z_to_bv 64 nZ
    if map_has h.vm_maps addr n then
      Ok (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [(addr, n)] [] [])
         (with_mmap_destroyed addr n
            (VmMaps.mkVmMapsFull h.vm_reserved (map_remove h.vm_maps addr)
               (maps_subtract h.vm_noaccess (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
               h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp) m) []
    else if munmap_free_ok h addr nZ then ret_outcome (Z_to_bv 64 0) m
    else Unmodeled

/-- Rocq: `munmap_witness_ok`. -/
theorem munmap_witness_ok (addr len : word) (i : SyscallInput) (m : Model) :
    munmap_spec addr len i m (munmap_witness addr len m) := by
  by_cases h1 : (!(bv_unsigned addr % page_size == 0) || w_is0 len) = true
  · simp only [munmap_spec, munmap_witness, h1, ↓reduceIte, err_ret, ret_only, ret_outcome,
      pure_iff]
  · by_cases h2 : TASK_SIZE < bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · simp only [munmap_spec, munmap_witness, h1, h2, Bool.false_eq_true, ↓reduceIte]
      refine bind_step _ _ i m (m_vmmaps m) m _ (get_vmmaps_ok i m) ?_
      simp only [err_ret, ret_only, ret_outcome, pure_iff]
    · by_cases h3 : map_has (m_vmmaps m).vm_maps addr
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
      · simp only [munmap_spec, munmap_witness, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
        refine bind_step _ _ i m (m_vmmaps m) m _ (get_vmmaps_ok i m) ?_
        simp only [h3, ↓reduceIte, set_vmmaps, forget_vm_range, bind_modify_iff, pure_iff,
          with_mmap_destroyed]
      · by_cases h4 : munmap_free_ok (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)) = true
        · simp only [munmap_spec, munmap_witness, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
          refine bind_step _ _ i m (m_vmmaps m) m _ (get_vmmaps_ok i m) ?_
          simp only [h3, h4, Bool.false_eq_true, ↓reduceIte, ret_only, ret_outcome, pure_iff]
        · simp only [munmap_spec, munmap_witness, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
          refine bind_step _ _ i m (m_vmmaps m) m _ (get_vmmaps_ok i m) ?_
          simp only [h3, h4, Bool.false_eq_true, ↓reduceIte, unmodeled_iff]

-- lean-port sentinel: ticket V-pilot-Mm-Mmap appends below this line

/-! ## The ledger and descriptor facts the registration owes — V-pilot-Mm-Mmap's half

Rocq: `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`'s `brk_r_ok_grow`,
`brk_grant_wf`, `brk_model_next_wf`, `check_brk_preserves` and
`check_munmap_preserves`, read at blob `b32c4db751c1`, the file at
f44244ad, the commit THE BASELINE above names; the file at this header's
`rocq-baseline` differs from it only in frame lemmas THE BASELINE lists,
every hunk at or after line 1588 on both sides and so after the five
(lines 1017-1191 at f44244ad), so the five read the same at either.  They
land here and not in
`Checks/VmMapsDisjoint.lean` for the reason WHY THE PRESERVES LEMMA IS
HERE gives for `check_mmap_preserves` — the invariant's file names no
checker and is frozen — and its own header sets the three brk lemmas
aside to land "beside `check_brk_preserves`".  The C ticket declared the
registration step not its own (WHAT IS NOT HERE, AND WHOSE IT IS, above),
and the preserves lemmas are the registration's first obligation, so the
pilot that registers the two arms writes them.

WHAT EACH SAYS.  `brk_r_ok_grow`: a strictly higher break is admitted by
`brk_r_ok` only through the branch that runs `brk_grow_ok` — the query
branch answers the old break, and the shrink branch answers the request
or the old break, both below it.  `brk_grant_wf`: the byte-granular grant
`[vm_brk, r)` a grow records overlaps no live page.  The gate tested the
pages `[PAGE_ALIGN(vm_brk), PAGE_ALIGN(r) + page_size)` for freedom, and
every page-aligned byte `p` of the grant lies inside them —
`PAGE_ALIGN(vm_brk) ≤ p` by `page_round_up_Z_le_aligned`, `p < r ≤
PAGE_ALIGN(r)` by `page_round_up_Z_ge` — while the two words the gate
built are exact because `PAGE_ALIGN(r) ≤ alloc_top` and `alloc_top +
stack_max_size < 2^64` (`State/Vm.lean`'s `alloc_top_room`) keep the
upper end inside the word: the `alloc_top_page_lt` line of the Rocq proof
is one `omega` here, as the invariant's header predicted.
`brk_model_next_wf`: a shrink is `maps_wf_subtract`, a grow is
`brk_grant_wf`, every other resolution leaves `vm_maps` as it was.  The
two `_preserves` lemmas walk their checker's arms in the order the four
soundness and completeness proofs above walk them — the same `by_cases`
chain — so a checker arm added later fails them with an unsolved goal
rather than passing by accident; an accepted `check_ret_only` arm keeps
the model (`check_ret_only_model`), the exact teardown is
`maps_wf_filter` over `map_remove`, and the accepted brk is
`brk_model_next_wf` through `vmm_brk_next`.

THE DESCRIPTOR FRAMES.  `Checks/Invariants.lean` registers two more
invariants, over `m_fd`, and its header says a checker's `m_fd` frame
belongs beside the checker — where its own two, for `exit` and `mmap`,
knowingly are not.  `check_brk_fd_state_frame` and
`check_munmap_fd_state_frame` are stated here, in their place.  Both rest
on `Model.mkModelOf m.m_fd …` being what every setter on the two paths
builds — `with_vmmaps`, `with_vm_backing` and so `vm_forget_range`, and
through them `with_mmap_destroyed` — each `rfl`, with `forget_vm_ranges`'s
fold over the unmap list the one induction. -/

/-! ### The brk ledger facts -/

/-- Rocq: `VmMapsDisjoint.brk_r_ok_grow`.  A grow resolution is gated:
`brk_r_ok` admits a strictly higher break only through the branch that
evaluates `brk_grow_ok`. -/
theorem brk_r_ok_grow (m : Model) (req r : word) (hok : brk_r_ok m req r = true)
    (hgrow : brk_is_grow req r (m_vmmaps m).vm_brk = true) : brk_grow_ok m req r = true := by
  simp only [brk_is_grow, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hgrow
  obtain ⟨⟨hreq, hpos⟩, hlt⟩ := hgrow
  by_cases hmin : bv_unsigned req < bv_unsigned (min_brk (m_vmmaps m))
  · simp only [brk_r_ok, hreq, hmin, Bool.false_or, decide_true, ↓reduceIte, bv_eqb_eq] at hok
    rw [hok] at hlt
    omega
  · by_cases hsh : bv_unsigned req < bv_unsigned (m_vmmaps m).vm_brk
    · simp only [brk_r_ok, hreq, hmin, hsh, Bool.false_or, decide_false,
        Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, bv_eqb_eq] at hok
      rcases hok with rfl | rfl <;> omega
    · simp only [brk_r_ok, hreq, hmin, hsh, Bool.false_or, decide_false, Bool.false_eq_true,
        ↓reduceIte, Bool.and_eq_true] at hok
      exact hok.2

/-- Rocq: `VmMapsDisjoint.brk_grant_wf`.  A brk grant may cover bytes the
gate never tested, but every PAGE-ALIGNED byte it covers lies inside the
range `region_free` did test, so the grant joins the ledger without
sharing a page with any live mapping. -/
theorem brk_grant_wf (m : Model) (req r : word) (hok : brk_r_ok m req r = true)
    (hgrow : brk_is_grow req r (m_vmmaps m).vm_brk = true) (hwf : vm_wf (m_vmmaps m)) :
    maps_wf (((m_vmmaps m).vm_brk, r - (m_vmmaps m).vm_brk) :: (m_vmmaps m).vm_maps) := by
  have hgok := brk_r_ok_grow m req r hok hgrow
  simp only [brk_is_grow, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hgrow
  obtain ⟨⟨_, hpos⟩, hlt⟩ := hgrow
  have hr := word_range r
  have hb := word_range (m_vmmaps m).vm_brk
  have hsz : bv_unsigned (r - (m_vmmaps m).vm_brk)
      = bv_unsigned r - bv_unsigned (m_vmmaps m).vm_brk := by
    have hle : (m_vmmaps m).vm_brk ≤ r := by
      rw [BitVec.le_def]; unfold bv_unsigned at hlt; omega
    unfold bv_unsigned at hlt ⊢
    rw [BitVec.toNat_sub_of_le hle]
    omega
  obtain ⟨hnz, hun⟩ := hwf
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · simp only [hsz]; omega
    · exact hnz e he
  · intro p hp
    simp only [owners]
    cases ho : owns_b ((m_vmmaps m).vm_brk, r - (m_vmmaps m).vm_brk) p
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact hun p hp
    · have ho' := owns_true _ _ _ ho
      rw [hsz] at ho'
      -- the gate ran, because a page-aligned byte of the grant is inside the rounded range
      simp only [brk_grow_ok, hpos, hlt, decide_true, Bool.true_and, ↓reduceIte,
        Bool.and_eq_true] at hgok
      obtain ⟨hgok, _⟩ := hgok
      have hlop : page_round_up_Z (bv_unsigned (m_vmmaps m).vm_brk) ≤ p :=
        page_round_up_Z_le_aligned _ _ hp (by omega)
      have hphi : p < page_round_up_Z (bv_unsigned r) := by
        have := page_round_up_Z_ge (bv_unsigned r) (by omega)
        omega
      have hlohi : page_round_up_Z (bv_unsigned (m_vmmaps m).vm_brk)
          < page_round_up_Z (bv_unsigned r) := by omega
      simp only [hlohi, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hgok
      obtain ⟨hceil, hfree⟩ := hgok
      have hroom := alloc_top_room (m_vmmaps m)
      have h64 : two_pow_64 = 18446744073709551616 := by decide
      have hsms : stack_max_size = 8388608 := by decide
      have hps : page_size = 4096 := rfl
      have hlo0 : 0 ≤ page_round_up_Z (bv_unsigned (m_vmmaps m).vm_brk) := by
        have := page_round_up_Z_ge (bv_unsigned (m_vmmaps m).vm_brk) (by omega)
        omega
      have hulo := u64 (page_round_up_Z (bv_unsigned (m_vmmaps m).vm_brk)) hlo0 (by omega)
      have hun' := u64 (page_round_up_Z (bv_unsigned r) + page_size
          - page_round_up_Z (bv_unsigned (m_vmmaps m).vm_brk)) (by omega) (by omega)
      have hown : owns_b (Z_to_bv 64 (page_round_up_Z (bv_unsigned (m_vmmaps m).vm_brk)),
          Z_to_bv 64 (page_round_up_Z (bv_unsigned r) + page_size
            - page_round_up_Z (bv_unsigned (m_vmmaps m).vm_brk))) p = true := by
        apply owns_intro
        · rw [hulo]; exact hlop
        · rw [hulo, hun']; omega
      rw [region_free_no_owner _ _ _ p (region_free_app_r _ _ _ _ hfree) hown]
      decide

/-- Rocq: `VmMapsDisjoint.brk_model_next_wf`.  The ledger after any admitted
brk resolution is well-formed: a shrink subtracts, a grow adds the grant
`brk_grant_wf` vouches for, and everything else keeps `vm_maps`. -/
theorem brk_model_next_wf (m : Model) (req r : word) (hok : brk_r_ok m req r = true)
    (hwf : vm_wf (m_vmmaps m)) : vm_wf (brk_model_next (m_vmmaps m) req r) := by
  unfold vm_wf brk_model_next brk_maps_next
  dsimp only
  by_cases hs : (decide (0 < bv_unsigned (m_vmmaps m).vm_brk)
      && decide (bv_unsigned r < bv_unsigned (m_vmmaps m).vm_brk)) = true
  · simp only [hs, ↓reduceIte]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    have hr := word_range r
    have hb := word_range (m_vmmaps m).vm_brk
    exact maps_wf_subtract _ _ _ (by omega) (by omega) (by omega) hwf
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    unfold brk_grants
    by_cases hg : brk_is_grow req r (m_vmmaps m).vm_brk = true
    · simp only [hg, ↓reduceIte, List.singleton_append]
      exact brk_grant_wf m req r hok hg hwf
    · simp only [hg, Bool.false_eq_true, ↓reduceIte, List.nil_append]
      exact hwf

/-! ### The two preserves lemmas -/

/-- Rocq: `VmMapsDisjoint.check_brk_preserves`.  The arm-level fact
`Checks/VmMapsDisjoint/Arms.lean`'s `arm_brk_preserves_vm` is built from. -/
theorem check_brk_preserves (req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_brk req eff m = CheckOk m' evs) (hwf : vm_wf (m_vmmaps m)) :
    vm_wf (m_vmmaps m') := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases cs <;> cases ci <;> simp only [check_brk, reduceCtorEq] at h
  by_cases hc : (brk_r_ok m req r && listNN_eqb zs (brk_zeros req r (m_vmmaps m).vm_brk)
      && listNN_eqb us (brk_unmaps r (m_vmmaps m).vm_brk)) = true
  · simp only [hc, ↓reduceIte, check_result.CheckOk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    rw [vmm_brk_next]
    exact brk_model_next_wf m req r hc.1.1 hwf
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `VmMapsDisjoint.check_munmap_preserves`.  The arm-level fact
`Checks/VmMapsDisjoint/Arms.lean`'s `arm_munmap_preserves_vm` is built
from: the three `check_ret_only` arms keep the model, and the exact
teardown filters an entry out of a well-formed ledger. -/
theorem check_munmap_preserves (addr len : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_munmap addr len eff m = CheckOk m' evs)
    (hwf : vm_wf (m_vmmaps m)) : vm_wf (m_vmmaps m') := by
  by_cases h1 : (!(bv_unsigned addr % page_size == 0) || w_is0 len) = true
  · simp only [check_munmap, h1, ↓reduceIte] at h
    rw [check_ret_only_model h]; exact hwf
  · by_cases h2 : TASK_SIZE < bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · simp only [check_munmap, h1, h2, Bool.false_eq_true, ↓reduceIte] at h
      rw [check_ret_only_model h]; exact hwf
    · by_cases h3 : map_has (m_vmmaps m).vm_maps addr
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
      · simp only [check_munmap, h1, h2, h3, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
        cases ws <;> cases zs <;> cases cs <;> cases ci <;> simp only [reduceCtorEq] at h
        by_cases hc : (w_is0 r
            && listNN_eqb us [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]) = true
        · simp only [hc, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          unfold vm_wf
          rw [vmm_mmap_destroyed]
          exact maps_wf_filter _ _ hwf
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      · by_cases h4 : munmap_free_ok (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)) = true
        · simp only [check_munmap, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte] at h
          rw [check_ret_only_model h]; exact hwf
        · simp only [check_munmap, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte,
            reduceCtorEq] at h

/-! ### The descriptor frames -/

/-- `vm_forget_range` is `with_vm_backing`, which carries `m.m_fd` across
(`State/Backing.lean`, `State/Model.lean`). -/
theorem fd_state_vm_forget_range (lo hi : Int) (m : Model) :
    (vm_forget_range lo hi m).m_fd = m.m_fd := rfl

/-- …and so does its fold over an unmap list. -/
theorem fd_state_forget_vm_ranges (rs : List (word × word)) (m : Model) :
    (forget_vm_ranges rs m).m_fd = m.m_fd := by
  induction rs generalizing m with
  | nil => rfl
  | cons e rest ih =>
    exact ih (vm_forget_range (bv_unsigned e.1) (bv_unsigned e.1 + bv_unsigned e.2) m)

/-- The accepted brk model is `with_vmmaps` under that fold. -/
theorem fd_state_with_brk_next (m : Model) (req r : word) :
    (with_brk_next m req r).m_fd = m.m_fd := by
  unfold with_brk_next
  exact fd_state_forget_vm_ranges _ _

/-- The accepted teardown is one `vm_forget_range` over `with_vmmaps`. -/
theorem fd_state_with_mmap_destroyed (a n : word) (h : VmMaps) (m : Model) :
    (with_mmap_destroyed a n h m).m_fd = m.m_fd := rfl

/-- `check_brk` writes the memory ledger and the lazy backing and nothing
else, so the descriptor subsystem is the one it was handed.  Lean-only:
the Rocq tree registers no `m_fd` invariant at all (THIS FILE MIRRORS
NOTHING, in `Checks/Invariants.lean`); the shape is that file's
`check_mmap_fd_state_frame`, with `check_brk_preserves`'s walk. -/
theorem check_brk_fd_state_frame (req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_brk req eff m = CheckOk m' evs) : m'.m_fd = m.m_fd := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases cs <;> cases ci <;> simp only [check_brk, reduceCtorEq] at h
  by_cases hc : (brk_r_ok m req r && listNN_eqb zs (brk_zeros req r (m_vmmaps m).vm_brk)
      && listNN_eqb us (brk_unmaps r (m_vmmaps m).vm_brk)) = true
  · simp only [hc, ↓reduceIte, check_result.CheckOk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fd_state_with_brk_next m req r
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- `check_munmap` likewise, with `check_munmap_preserves`'s walk. -/
theorem check_munmap_fd_state_frame (addr len : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_munmap addr len eff m = CheckOk m' evs) : m'.m_fd = m.m_fd := by
  by_cases h1 : (!(bv_unsigned addr % page_size == 0) || w_is0 len) = true
  · simp only [check_munmap, h1, ↓reduceIte] at h
    rw [check_ret_only_model h]
  · by_cases h2 : TASK_SIZE < bv_unsigned addr + page_round_up_Z (bv_unsigned len)
    · simp only [check_munmap, h1, h2, Bool.false_eq_true, ↓reduceIte] at h
      rw [check_ret_only_model h]
    · by_cases h3 : map_has (m_vmmaps m).vm_maps addr
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
      · simp only [check_munmap, h1, h2, h3, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
        cases ws <;> cases zs <;> cases cs <;> cases ci <;> simp only [reduceCtorEq] at h
        by_cases hc : (w_is0 r
            && listNN_eqb us [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]) = true
        · simp only [hc, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact fd_state_with_mmap_destroyed _ _ _ m
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      · by_cases h4 : munmap_free_ok (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)) = true
        · simp only [check_munmap, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte] at h
          rw [check_ret_only_model h]
        · simp only [check_munmap, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte,
            reduceCtorEq] at h

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap
