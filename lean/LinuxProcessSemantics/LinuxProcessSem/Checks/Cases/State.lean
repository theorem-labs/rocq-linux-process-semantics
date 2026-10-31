import LinuxProcessSemantics.LinuxProcessSem.State
import LinuxProcessSemantics.LinuxProcessSem.StreamLaws
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude

/-! # Checks.Cases.State — kernel pins for the `State` helpers

Pins for the ticket sections of `LinuxProcessSem/State.lean`, kept in
one file because both mirror one Rocq file.

Ticket A11: the VM ledger helpers `mremap` and `munmap` read, the
privilege test, and the `uname` pin.  Rocq keeps the corresponding
examples beside the syscalls that consume the helpers —
`Checks/Cases/Mm/Mremap.v` for the moved lazy range,
`Checks/Cases/Mm/Mmap.v` for the ownership invariant,
`Checks/Cases/Kernel/Sys.v` for the credential states — and each pin
below names the one it mirrors where there is one.

Ticket A8: the "Pipe helpers" block, `pipe_lookup` through
`pipe_fd_bytes`.  Every claim in that section is a claim about what the
kernel does, with the citation beside it — fs/pipe.c at Linux v6.18.46
(commit 1f99e9ab748f) throughout, the function named on each pin.  Each
pin has a positive half, the state or answer Linux's ring really holds,
and a negative half, the state a byte-counted or slot-blind port would
record and Linux's ring does not hold.  The arms that read the pipe
helpers — `pipe2`'s (`Checks/Arms/Fs/Pipe.lean`) and the pipe arms of
`read` and `write` — inherit these rather than re-deriving them.
`close` reads none: `close_spec` (`Sys/Fs/Open.lean`) and its checker
`check_close` are kind-blind, and what they leave the pipe table is
`pipe_table_survives_fd_remove` below.

Ticket A9: the stream and network read operations, `stream_take_z`,
`net_take`, `net_take_z` and `net_rest`, pinned against fs/pipe.c,
fs/read_write.c, net/ipv4/tcp.c, net/ipv4/tcp_input.c and
include/net/sock.h at the same commit, the line beside each claim; the laws the pins go through are the Rocq lemma twins in
`StreamLaws.lean`, which this file imports for that reason.

The errno block (ticket A1) is pinned after the A9 section: each value
against the asm-generic header that carries it, and the refutations
against the concrete mistakes those constants exist to prevent.
`theories/LinuxProcessSem/Checks/Cases/` has no `State.v`, so those pins
have no Rocq twin; the ticket A7, A3 and A12 sections follow it.

Ticket A12: the signal and terminal state — `with_killed` against
`with_halted`, `with_sigabrt_pending`, `with_sigaltstack_installed`,
`with_abort_terminal` and the stat pins.  Rocq keeps the corresponding
examples with the `tkill` arm (`Checks/Cases/Kernel/Signal.v`), which is
not ported, so the states are built by hand with the setters that arm
calls; the pins on the two terminal RULES are in `Checks/Cases/Run`.

Ticket A7: the descriptor allocator, `alloc_fd` and `alloc_fd2`.  Each
pin names the kernel source it is judged against — fs/file.c, fs/pipe.c
and net/socket.c at Linux v6.18.46 (commit 1f99e9ab748f), the function on
each pin — and each pin a plausible wrong allocator would flip has that
allocator's answer refuted beside it.

Not part of the trusted specification: this file is QA on the
definitions, written to be READ.  Each decision gets an accepting and a
rejecting instance, stated about what the kernel does; the executable
ones are closed by the kernel (`decide +kernel`, `decide`, `rfl`), never
the native-code decision tactic.

The iovec family (ticket A4) is pinned in its own section: the two
Linux limits and the scalar clamp, the import path's count gates and its
errno order, the single-descriptor short-circuit that caps before it
checks, the aggregate clamp, and the scatter/gather walks — each against
lib/iov_iter.c, fs/read_write.c, include/linux/iov_iter.h,
include/uapi/linux/uio.h and include/asm-generic/access_ok.h at Linux
v6.18.46 (commit 1f99e9ab748f), the function on each pin, with the lie a
reordered or wildcarded port would tell refuted beside it.  The one fixture
it shares with Rocq, `cap_boundary_iovecs`, is `Checks/Cases/Prelude.lean`'s,
which this file imports for it.

The user-memory reader pins (ticket A3) follow the A11 sections.  Each
states a concrete answer against the kernel's behaviour, with the file,
function and version the answer was read from, never against the Rocq
definition, and each decision carries a rejecting twin.  Rocq has no
check file of this name; the `access_okb` and wrapping pins were written
as the partial twin of `theories/LinuxProcessSem/Checks/Cases/Uaccess.v`,
whose lemma names they cite, before `Checks/Cases/Uaccess.lean` carried
the full twin — they stay as the reader-side statement of the same
facts — and the rest mirror nothing. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.State

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude (cap_boundary_iovecs)

/-! ## `map_has` / `map_remove`: munmap's whole-mapping case

The `map_remove` pins below cite nothing: the kernel argument sits on
`map_has`, whose answer selects the case `map_remove` then executes. -/

/-- `munmap` of exactly a recorded mapping is the modeled case… -/
theorem map_has_whole_mapping :
    map_has [(Z_to_bv 64 65536, Z_to_bv 64 8192)] (Z_to_bv 64 65536) (Z_to_bv 64 8192)
      = true := by decide +kernel

/-- …and a partial one is not: Linux would split the VMA
(`vms_gather_munmap_vmas` → `__split_vma`, mm/vma.c, Linux v6.18.46,
commit 1f99e9ab748f), which the model does not follow, so the half
inside a recorded mapping must NOT read as a whole one. -/
theorem map_has_rejects_partial_range :
    map_has [(Z_to_bv 64 65536, Z_to_bv 64 8192)] (Z_to_bv 64 65536) (Z_to_bv 64 4096)
      = false := by decide +kernel

/-- Nor is a range spanning two adjacent entries, even though one kernel
VMA could cover it: the model never merges entries, and answering "yes"
here would unmap under a ledger that still lists both. -/
theorem map_has_rejects_spanning_range :
    map_has [(Z_to_bv 64 65536, Z_to_bv 64 4096), (Z_to_bv 64 69632, Z_to_bv 64 4096)]
      (Z_to_bv 64 65536) (Z_to_bv 64 8192) = false := by decide +kernel

/-- The base is tested too, not only the size: a range of the recorded
LENGTH at another address is not the recorded mapping.  `do_vmi_munmap`
(mm/vma.c, Linux v6.18.46, commit 1f99e9ab748f) selects VMAs by the
address range `[start, end)`, so an equal-sized range one page up is a
different range and never the whole-mapping case.  A port that compared
sizes alone would answer `true` here. -/
theorem map_has_rejects_same_size_elsewhere :
    map_has [(Z_to_bv 64 65536, Z_to_bv 64 8192)] (Z_to_bv 64 69632) (Z_to_bv 64 8192)
      = false := by decide +kernel

/-- The scan is an ANY over the ledger, and an empty ledger has nothing:
a mapping listed second is found.  Every fixture above with a matching
entry is a singleton, where `all` and `any` agree, so a port with `all`
for `any` passed them all — and would answer false here and true for
every range on an empty ledger. -/
theorem map_has_finds_second_entry :
    map_has [(Z_to_bv 64 65536, Z_to_bv 64 4096), (Z_to_bv 64 131072, Z_to_bv 64 4096)]
      (Z_to_bv 64 131072) (Z_to_bv 64 4096) = true := by decide +kernel
theorem map_has_empty_ledger_has_nothing :
    map_has [] (Z_to_bv 64 65536) (Z_to_bv 64 4096) = false := by decide +kernel

/-- Unmapping the mapping based at `lo` takes out exactly that entry. -/
theorem map_remove_drops_the_based_entry :
    map_remove [(Z_to_bv 64 65536, Z_to_bv 64 4096), (Z_to_bv 64 131072, Z_to_bv 64 4096)]
      (Z_to_bv 64 65536) = [(Z_to_bv 64 131072, Z_to_bv 64 4096)] := by decide +kernel

/-- An entry that merely CONTAINS `lo` is not based there and stays: the
whole-mapping case keys on the base, not on membership. -/
theorem map_remove_keeps_a_containing_entry :
    map_remove [(Z_to_bv 64 65536, Z_to_bv 64 8192)] (Z_to_bv 64 69632)
      = [(Z_to_bv 64 65536, Z_to_bv 64 8192)] := by decide +kernel

/-! ## `vm_backed_bytes`: exposed capacity, not occupancy

Ledger arithmetic, so no kernel line is cited: which of the two measures
a site asks is argued on the Rocq definition. -/

/-- A PROT_NONE hole is not exposed capacity: one 8 KiB mapping with a
4 KiB inaccessible interval exposes 4 KiB… -/
theorem vm_backed_bytes_cuts_noaccess :
    vm_backed_bytes
      (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 65536, Z_to_bv 64 8192)]
        [(Z_to_bv 64 65536, Z_to_bv 64 4096)] (Z_to_bv 64 0) (Z_to_bv 64 0) 0
        (Z_to_bv 64 0) (Z_to_bv 64 0)) = 4096 := by decide +kernel

/-- …not the 8 KiB `vm_live_bytes` counts, which is virtual occupancy. -/
theorem vm_backed_bytes_is_not_live_bytes :
    vm_backed_bytes
      (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 65536, Z_to_bv 64 8192)]
        [(Z_to_bv 64 65536, Z_to_bv 64 4096)] (Z_to_bv 64 0) (Z_to_bv 64 0) 0
        (Z_to_bv 64 0) (Z_to_bv 64 0)) ≠ 8192 := by decide +kernel

/-! ## `page_in_half_open` / `move_page_base`

Arithmetic helpers of `vm_resize_backing`; the kernel argument sits on
its pins in the next section, and these only fix the half-openness and
the offset arithmetic they contribute. -/

/-- `[lo, hi)` is half-open: the first page is in, the page at `hi` is out. -/
theorem page_in_half_open_lo : page_in_half_open 65536 69632 (Z_to_bv 64 65536) = true := by
  decide +kernel
theorem page_in_half_open_hi : page_in_half_open 65536 69632 (Z_to_bv 64 69632) = false := by
  decide +kernel

/-- A moved page keeps its offset inside the mapping: the second page of
`[65536, …)` moved to 131072 lands at 135168, not at the destination base. -/
theorem move_page_base_keeps_offset :
    move_page_base (Z_to_bv 64 65536) (Z_to_bv 64 131072) (Z_to_bv 64 69632)
      = Z_to_bv 64 135168 := by decide +kernel
theorem move_page_base_is_not_dst :
    move_page_base (Z_to_bv 64 65536) (Z_to_bv 64 131072) (Z_to_bv 64 69632)
      ≠ Z_to_bv 64 131072 := by decide +kernel

/-! ## `vm_resize_backing`: the moved lazy range

The fixtures `Checks/Cases/Mm/Mremap.v` builds its ledger pins on: a
MAP_NORESERVE mapping of one page, touched (`mremap_lazy_one_page`), and
one of two pages, both touched (`mremap_lazy_two_pages`).  The `vm_maps`
half is the caller's business (`mremap_maps_next`); only the two backing
ledgers are read here. -/

def mremap_lazy_one_page : Model :=
  with_vm_backing [(Z_to_bv 64 65536, Z_to_bv 64 4096)] [Z_to_bv 64 65536]
    (mkModel [] (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 65536, Z_to_bv 64 4096)] []
                  (Z_to_bv 64 0) (Z_to_bv 64 0) 4096 (Z_to_bv 64 0) (Z_to_bv 64 0))
       IEof [] none none none)

def mremap_lazy_two_pages : Model :=
  with_vm_backing [(Z_to_bv 64 65536, Z_to_bv 64 8192)] [Z_to_bv 64 65536, Z_to_bv 64 69632]
    (mkModel [] (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 65536, Z_to_bv 64 8192)] []
                  (Z_to_bv 64 0) (Z_to_bv 64 0) 8192 (Z_to_bv 64 0) (Z_to_bv 64 0))
       IEof [] none none none)

/-- Rocq's `mremap_model_next` (Sys/Mm/Mremap.v at f44244ad) applies
`vm_resize_backing` AFTER `mremap_maps_next` has replaced the one
`vm_maps` entry with the destination, and `vm_backing_used` reads both
ledgers, so the charge pins below need that replacement too.  These pins
predate the port of `Sys/Mm/Mremap.v` (PR #810), so the three replaced
ledgers are written out here by hand rather than through
`mremap_model_next`: the mapping moved to 131072 and grown, grown in
place, and shrunk in place. -/
def mremap_lazy_one_page_moved : Model :=
  with_vmmaps (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 131072, Z_to_bv 64 8192)] []
                (Z_to_bv 64 0) (Z_to_bv 64 0) 4096 (Z_to_bv 64 0) (Z_to_bv 64 0))
    mremap_lazy_one_page
def mremap_lazy_one_page_grown : Model :=
  with_vmmaps (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 65536, Z_to_bv 64 8192)] []
                (Z_to_bv 64 0) (Z_to_bv 64 0) 4096 (Z_to_bv 64 0) (Z_to_bv 64 0))
    mremap_lazy_one_page
def mremap_lazy_two_pages_shrunk : Model :=
  with_vmmaps (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 65536, Z_to_bv 64 4096)] []
                (Z_to_bv 64 0) (Z_to_bv 64 0) 8192 (Z_to_bv 64 0) (Z_to_bv 64 0))
    mremap_lazy_two_pages

/-- THE PIN: a moved lazy range.  `mremap(65536, 4096, 8192, MAYMOVE)`
answered at 131072 carries the one touched page to 131072 and reserves
the grown range there, exactly as Rocq's
`mremap_lazy_move_ledgers_follow_contents` states of `mremap_model_next`
(`Checks/Cases/Mm/Mremap.v`): the page tables move with the mapping
(`copy_vma_and_data` → `move_page_tables`, mm/mremap.c, Linux v6.18.46,
commit 1f99e9ab748f) and the grown tail is untouched, so the charge
stays at the one page. -/
theorem vm_resize_backing_move_lazy :
    m_vm_lazy (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 4096)
                 (Z_to_bv 64 131072) (Z_to_bv 64 8192) mremap_lazy_one_page_moved)
      = [(Z_to_bv 64 131072, Z_to_bv 64 8192)]
    ∧ vm_backing_used (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 4096)
                         (Z_to_bv 64 131072) (Z_to_bv 64 8192) mremap_lazy_one_page_moved)
      = 4096 := by decide +kernel
theorem vm_resize_backing_move_materialized :
    m_vm_materialized (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 4096)
                         (Z_to_bv 64 131072) (Z_to_bv 64 8192) mremap_lazy_one_page_moved)
      = [Z_to_bv 64 131072] := by decide +kernel

/-- Each moved page keeps its OFFSET within the mapping: the two pages of
`mremap_lazy_two_pages` land at `dst` and `dst + 4096`, in ledger order.
Every other move fixture carries one materialized page, so a port that
sent every page to `dst` passed them all; `move_page_base_keeps_offset`
pins the helper, this pins its use. -/
theorem vm_resize_backing_move_keeps_page_offsets :
    m_vm_materialized (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 8192)
                         (Z_to_bv 64 131072) (Z_to_bv 64 8192) mremap_lazy_two_pages)
      = [Z_to_bv 64 131072, Z_to_bv 64 135168] ∧
    m_vm_materialized (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 8192)
                         (Z_to_bv 64 131072) (Z_to_bv 64 8192) mremap_lazy_two_pages)
      ≠ [Z_to_bv 64 131072, Z_to_bv 64 131072] := by decide +kernel

/-- The charge conjunct is not free: applied to the UNREPLACED ledger,
`vm_resize_backing` alone leaves the old entry's eager bytes and the
moved page both charged, so a port that resized the backing without
`mremap_maps_next`'s replacement would over-charge by a page. -/
theorem vm_resize_backing_charge_needs_maps_replacement :
    vm_backing_used (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 4096)
                       (Z_to_bv 64 131072) (Z_to_bv 64 8192) mremap_lazy_one_page)
      = 8192 := by decide +kernel

/-- The rejecting half of the pin: the moved page is NOT left at its old
address, and it is NOT counted twice.  A port that moved the lazy range
but forgot the pages would leave the ledger at `[65536]`; one that copied
instead of moved would list both. -/
theorem vm_resize_backing_move_leaves_nothing_behind :
    m_vm_materialized (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 4096)
                         (Z_to_bv 64 131072) (Z_to_bv 64 8192) mremap_lazy_one_page)
      ≠ [Z_to_bv 64 65536] := by decide +kernel
theorem vm_resize_backing_move_does_not_copy :
    m_vm_materialized (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 4096)
                         (Z_to_bv 64 131072) (Z_to_bv 64 8192) mremap_lazy_one_page)
      ≠ [Z_to_bv 64 131072, Z_to_bv 64 65536] := by decide +kernel

/-- A shrink in place releases the cut page's charge (`shrink_vma`,
mm/mremap.c, → `do_vmi_munmap` of the excess, mm/vma.c, Linux v6.18.46,
commit 1f99e9ab748f): Rocq's `mremap_lazy_shrink_ledgers_are_exact`,
charge included. -/
theorem vm_resize_backing_shrink_releases_tail :
    m_vm_lazy (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 8192)
                 (Z_to_bv 64 65536) (Z_to_bv 64 4096) mremap_lazy_two_pages_shrunk)
      = [(Z_to_bv 64 65536, Z_to_bv 64 4096)]
    ∧ m_vm_materialized (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 8192)
                           (Z_to_bv 64 65536) (Z_to_bv 64 4096) mremap_lazy_two_pages_shrunk)
      = [Z_to_bv 64 65536]
    ∧ vm_backing_used (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 8192)
                         (Z_to_bv 64 65536) (Z_to_bv 64 4096) mremap_lazy_two_pages_shrunk)
      = 4096 := by decide +kernel

/-- A shrinking MOVE does not carry the cut page along: the tail beyond
the new size is unmapped, not relocated, so 69632 neither stays nor
reappears at 135168. -/
theorem vm_resize_backing_shrinking_move_drops_cut_page :
    m_vm_materialized (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 8192)
                         (Z_to_bv 64 131072) (Z_to_bv 64 4096) mremap_lazy_two_pages)
      = [Z_to_bv 64 131072] := by decide +kernel

/-- A lazy grow in place keeps only the old charge; the grown tail starts
unmaterialized (a `pte_none` fault on a private anonymous VMA is served
by `do_pte_missing` → `do_anonymous_page`, mm/memory.c, Linux v6.18.46,
commit 1f99e9ab748f, from the zero page or a zeroed folio): Rocq's
`mremap_lazy_grow_preserves_only_old_charge`, charge included. -/
theorem vm_resize_backing_grow_keeps_old_charge :
    m_vm_lazy (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 4096)
                 (Z_to_bv 64 65536) (Z_to_bv 64 8192) mremap_lazy_one_page_grown)
      = [(Z_to_bv 64 65536, Z_to_bv 64 8192)]
    ∧ m_vm_materialized (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 4096)
                           (Z_to_bv 64 65536) (Z_to_bv 64 8192) mremap_lazy_one_page_grown)
      = [Z_to_bv 64 65536]
    ∧ vm_backing_used (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 4096)
                         (Z_to_bv 64 65536) (Z_to_bv 64 8192) mremap_lazy_one_page_grown)
      = 4096 := by decide +kernel

/-- Stale destination metadata cannot manufacture backing: a hand-built
ledger already listing 131072 as materialized ends with ONE page there
after the move, not two. -/
theorem vm_resize_backing_clears_stale_destination :
    m_vm_materialized (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 4096)
                         (Z_to_bv 64 131072) (Z_to_bv 64 8192)
                         (with_vm_backing [(Z_to_bv 64 65536, Z_to_bv 64 4096)]
                            [Z_to_bv 64 65536, Z_to_bv 64 131072] mremap_lazy_one_page))
      = [Z_to_bv 64 131072] := by decide +kernel

/-- The same for the LAZY ledger: a hand-built ledger already carrying a
lazy range at 131072 ends with exactly the moved mapping's range there,
not that range beside the stale one.  `vm_resize_backing`'s docstring
promises destination metadata is removed from BOTH ledgers; the pin
above exercises only the materialized one. -/
theorem vm_resize_backing_clears_stale_lazy_destination :
    m_vm_lazy (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 4096)
                 (Z_to_bv 64 131072) (Z_to_bv 64 8192)
                 (with_vm_backing [(Z_to_bv 64 65536, Z_to_bv 64 4096),
                                   (Z_to_bv 64 131072, Z_to_bv 64 4096)]
                    [Z_to_bv 64 65536] mremap_lazy_one_page))
      = [(Z_to_bv 64 131072, Z_to_bv 64 8192)] ∧
    m_vm_lazy (vm_resize_backing true (Z_to_bv 64 65536) (Z_to_bv 64 4096)
                 (Z_to_bv 64 131072) (Z_to_bv 64 8192)
                 (with_vm_backing [(Z_to_bv 64 65536, Z_to_bv 64 4096),
                                   (Z_to_bv 64 131072, Z_to_bv 64 4096)]
                    [Z_to_bv 64 65536] mremap_lazy_one_page))
      ≠ [(Z_to_bv 64 131072, Z_to_bv 64 8192), (Z_to_bv 64 131072, Z_to_bv 64 4096)] := by
  decide +kernel

/-- An EAGER source has no lazy provenance to carry: the move records no
lazy range at the destination and moves no page. -/
theorem vm_resize_backing_eager_source_moves_nothing :
    m_vm_lazy (vm_resize_backing false (Z_to_bv 64 65536) (Z_to_bv 64 4096)
                 (Z_to_bv 64 131072) (Z_to_bv 64 8192) mremap_lazy_one_page) = []
    ∧ m_vm_materialized (vm_resize_backing false (Z_to_bv 64 65536) (Z_to_bv 64 4096)
                           (Z_to_bv 64 131072) (Z_to_bv 64 8192) mremap_lazy_one_page)
      = [] := by decide +kernel

/-! ## `noaccess_pages_owned`: the ownership invariant

The two brk states `Checks/Cases/Mm/Mmap.v` measures against it.  The
real one: a same-page brk shrink to 69620 truncated the brk entry to
`(65536, 4084)` while the page-rounded protected range `(65536, 4096)`
stayed whole.  The counterfactual: the residual entry taken away and a
mapping placed elsewhere. -/

def m_brk_same_page_shrunk_maps : VmMaps :=
  VmMaps.mkVmMapsFull [] [(Z_to_bv 64 65536, Z_to_bv 64 4084)]
    [(Z_to_bv 64 65536, Z_to_bv 64 4096)] (Z_to_bv 64 65536) (Z_to_bv 64 69620) 0
    (Z_to_bv 64 0) (Z_to_bv 64 0)

/-- The protected interval is CUT OUT of the live entries, not subtracted
from their total: on this shrunken brk state, whose protected page
`(65536, 4096)` overhangs the live entry `(65536, 4084)`, the exposed
capacity is 0 — a port that subtracted the protected total from the live
total would answer −12, a negative capacity no ledger has.  Every other
`vm_backed_bytes` fixture keeps its protected entries inside the live
ones, where the two computations agree. -/
theorem vm_backed_bytes_cuts_not_subtracts :
    vm_backed_bytes m_brk_same_page_shrunk_maps = 0 ∧
    vm_backed_bytes m_brk_same_page_shrunk_maps ≠ -12 := by decide +kernel

def m_overhanging_noaccess_maps : VmMaps :=
  VmMaps.mkVmMapsFull [] [(Z_to_bv 64 65536, Z_to_bv 64 8192)]
    [(Z_to_bv 64 69632, Z_to_bv 64 8192)] (Z_to_bv 64 0) (Z_to_bv 64 0) 0
    (Z_to_bv 64 0) (Z_to_bv 64 0)

/-- Nor is it a CLAMPED subtraction: a protected interval overhanging the
live entry costs only the overlap.  Live `[65536, 73728)` against
protected `[69632, 77824)` leaves one page exposed; `max 0 (live −
protected)` would answer 0, and agrees with the cut on every fixture
whose protected entries sit inside the live ones — including the one
above, where both give 0. -/
theorem vm_backed_bytes_cuts_not_clamped_subtracts :
    vm_backed_bytes m_overhanging_noaccess_maps = 4096 ∧
    vm_backed_bytes m_overhanging_noaccess_maps ≠ 0 := by decide +kernel

def m_two_live_entries_maps : VmMaps :=
  VmMaps.mkVmMapsFull [] [(Z_to_bv 64 65536, Z_to_bv 64 4096), (Z_to_bv 64 131072, Z_to_bv 64 8192)]
    [] (Z_to_bv 64 0) (Z_to_bv 64 0) 0 (Z_to_bv 64 0) (Z_to_bv 64 0)

/-- `live_bytes` SUMS the ledger: entries of one and two pages are three
pages, not the first entry's size and not a page per entry.  Every other
fixture reaches it through a list that is empty or one entry long after
the cuts, where all three agree. -/
theorem vm_live_bytes_sums_every_entry :
    vm_live_bytes m_two_live_entries_maps = 12288 ∧
    vm_live_bytes m_two_live_entries_maps ≠ 4096 ∧
    vm_live_bytes m_two_live_entries_maps ≠ 8192 := by decide +kernel

def m_brk_orphan_without_residual_maps : VmMaps :=
  VmMaps.mkVmMapsFull [] [(Z_to_bv 64 131072, Z_to_bv 64 4096)]
    [(Z_to_bv 64 65536, Z_to_bv 64 4096)] (Z_to_bv 64 65536) (Z_to_bv 64 69620) 0
    (Z_to_bv 64 0) (Z_to_bv 64 0)

/-- The invariant HOLDS on the real shrunken state: the orphan
`[69620, 69632)` is on page `[65536, 69632)`, which the truncated brk
entry still reaches into (Rocq: `noaccess_pages_owned_brk_orphan`). -/
theorem noaccess_pages_owned_brk_orphan :
    noaccess_pages_owned m_brk_same_page_shrunk_maps := by
  intro a n hin
  simp only [m_brk_same_page_shrunk_maps, List.mem_singleton, Prod.mk.injEq] at hin
  obtain ⟨rfl, rfl⟩ := hin
  have e65536 : bv_unsigned (Z_to_bv 64 65536) = 65536 := by decide +kernel
  have e4096 : bv_unsigned (Z_to_bv 64 4096) = 4096 := by decide +kernel
  have e4084 : bv_unsigned (Z_to_bv 64 4084) = 4084 := by decide +kernel
  refine ⟨by rw [e4096]; omega, ?_⟩
  intro x hx
  rw [e65536, e4096] at hx
  refine ⟨Z_to_bv 64 65536, Z_to_bv 64 4084, List.mem_singleton.mpr rfl, ?_⟩
  rw [e65536, e4084]
  simp only [page_round_down_Z, page_size]
  omega

/-- And it FAILS on the counterfactual, so it is not vacuous: no live
entry touches the orphan's page once the residual is gone (Rocq:
`noaccess_pages_owned_fails_without_residual`). -/
theorem noaccess_pages_owned_fails_without_residual :
    ¬ noaccess_pages_owned m_brk_orphan_without_residual_maps := by
  intro h
  have e65536 : bv_unsigned (Z_to_bv 64 65536) = 65536 := by decide +kernel
  have e4096 : bv_unsigned (Z_to_bv 64 4096) = 4096 := by decide +kernel
  have e131072 : bv_unsigned (Z_to_bv 64 131072) = 131072 := by decide +kernel
  obtain ⟨_, hpage⟩ := h (Z_to_bv 64 65536) (Z_to_bv 64 4096)
    (by simp only [m_brk_orphan_without_residual_maps, List.mem_singleton])
  obtain ⟨b, s, hin, hb1, _⟩ := hpage 65536 (by rw [e65536, e4096]; omega)
  simp only [m_brk_orphan_without_residual_maps, List.mem_singleton, Prod.mk.injEq] at hin
  obtain ⟨rfl, rfl⟩ := hin
  rw [e131072] at hb1
  simp only [page_round_down_Z, page_size] at hb1
  omega

/-- Ownership is by the PAGE, half-open on both sides: a live entry that
starts exactly at the next page does not own a protected page that ends
there… -/
theorem noaccess_pages_owned_rejects_next_page_neighbour :
    ¬ noaccess_pages_owned
        (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 69632, Z_to_bv 64 4096)]
          [(Z_to_bv 64 65536, Z_to_bv 64 4096)] (Z_to_bv 64 0) (Z_to_bv 64 0) 0
          (Z_to_bv 64 0) (Z_to_bv 64 0)) := by
  intro h
  have e65536 : bv_unsigned (Z_to_bv 64 65536) = 65536 := by decide +kernel
  have e4096 : bv_unsigned (Z_to_bv 64 4096) = 4096 := by decide +kernel
  have e69632 : bv_unsigned (Z_to_bv 64 69632) = 69632 := by decide +kernel
  obtain ⟨_, hpage⟩ := h (Z_to_bv 64 65536) (Z_to_bv 64 4096) (by simp only [List.mem_singleton])
  obtain ⟨b, s, hin, hb1, _⟩ := hpage 65536 (by rw [e65536, e4096]; omega)
  simp only [List.mem_singleton, Prod.mk.injEq] at hin
  obtain ⟨rfl, rfl⟩ := hin
  rw [e69632] at hb1
  simp only [page_round_down_Z, page_size] at hb1
  omega

/-- …and one that ends exactly at the protected page's start does not own
it either.  `≤` at the first bound of the page test would call the
next-page neighbour an owner, `≤` at the second the previous-page one;
either lets the allocator place over the hole, and the pair of pins
covers both. -/
theorem noaccess_pages_owned_rejects_previous_page_neighbour :
    ¬ noaccess_pages_owned
        (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 61440, Z_to_bv 64 4096)]
          [(Z_to_bv 64 65536, Z_to_bv 64 4096)] (Z_to_bv 64 0) (Z_to_bv 64 0) 0
          (Z_to_bv 64 0) (Z_to_bv 64 0)) := by
  intro h
  have e65536 : bv_unsigned (Z_to_bv 64 65536) = 65536 := by decide +kernel
  have e4096 : bv_unsigned (Z_to_bv 64 4096) = 4096 := by decide +kernel
  have e61440 : bv_unsigned (Z_to_bv 64 61440) = 61440 := by decide +kernel
  obtain ⟨_, hpage⟩ := h (Z_to_bv 64 65536) (Z_to_bv 64 4096) (by simp only [List.mem_singleton])
  obtain ⟨b, s, hin, _, hb2⟩ := hpage 65536 (by rw [e65536, e4096]; omega)
  simp only [List.mem_singleton, Prod.mk.injEq] at hin
  obtain ⟨rfl, rfl⟩ := hin
  rw [e61440, e4096] at hb2
  simp only [page_round_down_Z, page_size] at hb2
  omega

/-- Ownership is asked of EVERY page of the protected range, not of its
first: a two-page protected range whose second page no live entry
touches is an orphan even though its first page is owned.  Every other
protected fixture is one page, where the base page is the only page, so
a port that tested the entry's first byte alone passed them all — and
would let the allocator place over the second page, the hole the
invariant exists to keep it off. -/
theorem noaccess_pages_owned_rejects_orphan_second_page :
    ¬ noaccess_pages_owned
        (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 65536, Z_to_bv 64 4096)]
          [(Z_to_bv 64 65536, Z_to_bv 64 8192)] (Z_to_bv 64 0) (Z_to_bv 64 0) 0
          (Z_to_bv 64 0) (Z_to_bv 64 0)) := by
  intro h
  have e65536 : bv_unsigned (Z_to_bv 64 65536) = 65536 := by decide +kernel
  have e4096 : bv_unsigned (Z_to_bv 64 4096) = 4096 := by decide +kernel
  have e8192 : bv_unsigned (Z_to_bv 64 8192) = 8192 := by decide +kernel
  obtain ⟨_, hpage⟩ := h (Z_to_bv 64 65536) (Z_to_bv 64 8192) (by simp only [List.mem_singleton])
  obtain ⟨b, s, hin, _, hb2⟩ := hpage 69632 (by rw [e65536, e8192]; omega)
  simp only [List.mem_singleton, Prod.mk.injEq] at hin
  obtain ⟨rfl, rfl⟩ := hin
  rw [e65536, e4096] at hb2
  simp only [page_round_down_Z, page_size] at hb2
  omega

/-- The nonemptiness conjunct bites: an EMPTY protected entry, which no
writer produces, fails the invariant even when its base is owned. -/
theorem noaccess_pages_owned_rejects_empty_entry :
    ¬ noaccess_pages_owned
        (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 65536, Z_to_bv 64 4096)]
          [(Z_to_bv 64 65536, Z_to_bv 64 0)] (Z_to_bv 64 0) (Z_to_bv 64 0) 0
          (Z_to_bv 64 0) (Z_to_bv 64 0)) := by
  intro h
  obtain ⟨hpos, _⟩ := h (Z_to_bv 64 65536) (Z_to_bv 64 0) (by simp only [List.mem_singleton])
  have e0 : bv_unsigned (Z_to_bv 64 0) = 0 := by decide +kernel
  rw [e0] at hpos
  omega

/-! ## `creds_privileged`: the effective uid, and only it

Every claim is about security/commoncap.c at Linux v6.18.46 (commit
1f99e9ab748f), under the standing assumptions the Rocq definition
names (init user namespace, no file or ambient capabilities, default
securebits, unnarrowed bounding set). -/

/-- Root is privileged: `cap_bprm_creds_from_file` (security/commoncap.c,
Linux v6.18.46, commit 1f99e9ab748f) sets `cap_effective = cap_permitted`
when `handle_privileged_root` (same file and version) reports the new
euid as root (`__is_eff(root_uid, new)` → `*effective = true`),
CAP_SETUID included. -/
theorem creds_privileged_root :
    creds_privileged (Creds.mkCreds (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
      (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) []) = true := by decide +kernel

/-- So is a set-user-ID-root process whose REAL uid is not 0: the same
`handle_privileged_root` test (security/commoncap.c, Linux v6.18.46,
commit 1f99e9ab748f) reads the effective uid, not the real one. -/
theorem creds_privileged_setuid_root :
    creds_privileged (Creds.mkCreds (Z_to_bv 64 1000) (Z_to_bv 64 0) (Z_to_bv 64 0)
      (Z_to_bv 64 1000) (Z_to_bv 64 1000) (Z_to_bv 64 1000) []) = true := by decide +kernel

/-- Root that has dropped its EFFECTIVE uid is not: `cap_emulate_setxuid`
(security/commoncap.c, Linux v6.18.46, commit 1f99e9ab748f) clears
`cap_effective` on every euid 0 → non-0 transition
(`if (uid_eq(old->euid, root_uid) && !uid_eq(new->euid, root_uid))
cap_clear(new->cap_effective)`), so after `seteuid(1000)` a `setgroups`
returns -EPERM (`setgroups` → `may_setgroups` →
`ns_capable_setid(user_ns, CAP_SETGID)`, kernel/groups.c, same version)
even though uid and suid are still 0.  A port keyed on the real uid
would say the opposite. -/
theorem creds_privileged_rejects_real_uid_zero :
    creds_privileged (Creds.mkCreds (Z_to_bv 64 0) (Z_to_bv 64 1000) (Z_to_bv 64 0)
      (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) []) = false := by decide +kernel

/-- Group 0 grants nothing: CAP_SETGID is a capability bit, and
`cap_emulate_setxuid` (security/commoncap.c, Linux v6.18.46, commit
1f99e9ab748f) compares uids only, so an egid of 0 beside a non-zero
euid is unprivileged. -/
theorem creds_privileged_rejects_egid_zero :
    creds_privileged (Creds.mkCreds (Z_to_bv 64 1000) (Z_to_bv 64 1000) (Z_to_bv 64 1000)
      (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) []) = false := by decide +kernel

/-- Privilege is euid ZERO, not a low euid: `cap_emulate_setxuid`
(security/commoncap.c, Linux v6.18.46, commit 1f99e9ab748f) tests
`uid_eq(…, root_uid)` against each id and nothing about a value below
root (its one other input, `issecure(SECURE_KEEP_CAPS)`, is a securebit
the modeled process never sets), so euid 1 — a system account on most
distributions — is as unprivileged as 1000.  Every other
unprivileged fixture here uses 1000, which a port keyed on `euid < 1000`
would also refuse. -/
theorem creds_privileged_rejects_euid_one :
    creds_privileged (Creds.mkCreds (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1)
      (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) []) = false := by decide +kernel

/-! ## The `uname` pin -/

/-- A fresh exec has observed no UTS name: `init_model` starts the pin at
`none`, so the FIRST `uname` is where the kernel identity enters. -/
theorem m_utsname_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_utsname (init_model reserved brk0 mbase sp lim inp) = none := rfl

/-- The pin is not the other `Option (List byte)` pin.  RLIMIT_CORE's
(`prlimit64`) and `uname`'s are the pair a port could cross-wire; each
setter leaves the other's accessor alone. -/
theorem uname_pin_is_not_rlimit_core (bs : List byte) (m : Model) :
    m_rlimit_core (with_utsname bs m) = m_rlimit_core m
    ∧ m_utsname (with_rlimit_core bs m) = m_utsname m := ⟨rfl, rfl⟩

/-- Once pinned, a second `uname` reads the same bytes, whatever else the
process did in between.  What this rests on: `utsname()` is
`&current->nsproxy->uts_ns->name` (include/linux/utsname.h, Linux
v6.18.46, commit 1f99e9ab748f), one record per UTS namespace, and the
modeled process never writes it — `sethostname` and `setdomainname`
(kernel/sys.c) have no arm, and nothing in the model opens
/proc/sys/kernel/hostname or domainname (`proc_do_uts_string`,
kernel/utsname_sysctl.c, the third writer).  `sysname` is a static
initializer (`init_uts_ns`, init/version-timestamp.c, Linux v6.18.46);
`nodename` starts as `UTS_NODENAME` in the same initializer, is
overwritten at boot by `early_hostname` (init/version.c, v6.18.46) when
the `hostname=` parameter is given or by IP autoconfiguration
(net/ipv4/ipconfig.c, under `CONFIG_IP_PNP`) — both `__init`, before any
process runs — and after that only by userspace.  ANOTHER process in
the same namespace can change `nodename` between two `uname`s, so the
pin is right only while the environment is quiescent for the run;
bugs/uname-pin-rests-on-uts-namespace-quiescence.md carries that
premise. -/
theorem uname_pin_survives_other_setters (bs : List byte) (v : word) (c : Creds) (m : Model) :
    m_utsname (with_sigmask v (with_creds c (with_tid v (with_utsname bs m)))) = some bs := rfl

/-! ## Ticket A8: the pipe helpers -/
/-! ## `pipe_write_room`: one slot, and the page's high-water mark -/

/-- A write of exactly `PIPE_BUF` into an empty pipe fits in one slot:
`anon_pipe_write`'s merge path is skipped (`was_empty`, :478) and the
loop at :500 fills one fresh page (:515, :522) and stops (:544-545). -/
theorem pipe_room_empty_pipe_buf :
    pipe_write_room ([], 0) PIPE_BUF = true := by decide

/-- One byte more than `PIPE_BUF` needs a second page: `anon_pipe_write`'s
loop at :500 continues past the first, and the one-slot model refuses rather than
records a second slot. -/
theorem pipe_room_empty_over_pipe_buf :
    pipe_write_room ([], 0) (PIPE_BUF + 1) = false := by decide

/-- An empty queue means a released slot (`anon_pipe_read`, :359-362), so
the mark a drained page carried is irrelevant to the next write: the room
test on an empty queue reads only `n`, whatever `used` says.  A port that
tested `used + n` on every queue would refuse a fresh page it should
grant. -/
theorem pipe_room_empty_ignores_mark (u n : Int) :
    pipe_write_room ([], u) n = decide (n ≤ PIPE_BUF) := rfl

/-- THE PIN TICKET A8 ASKS FOR: a write `pipe_write_room` refuses is never
appended whole.  Appending it anyway would leave the mark past the page —
`anon_pipe_write`'s `offset + chars <= PAGE_SIZE` at :482-483 fails, and
Linux puts those bytes on a second page (:500, :515) the one-slot model does not account —
so an arm that appends without consulting the room would record a slot
Linux's ring does not hold in one page.  Stated for every queue and every
write. -/
theorem pipe_append_past_room_overflows_page (st : PipeBuf) (bs : List byte) :
    pipe_write_room st (bs.length : Int) = false →
    PIPE_BUF < (pipe_append st bs).2 := by
  intro h
  obtain ⟨q, used⟩ := st
  cases q with
  | nil =>
    simp only [pipe_write_room, decide_eq_false_iff_not, Int.not_le] at h
    simp only [pipe_append]
    exact h
  | cons b q' =>
    simp only [pipe_write_room, decide_eq_false_iff_not, Int.not_le] at h
    simp only [pipe_append]
    omega

/-- The converse, so the pin above is not vacuous: a write the room admits
lands with the mark inside the page, which is the merge (`anon_pipe_write`,
:482-483) or the single fresh page (:500-522) it performs. -/
theorem pipe_append_within_room_fits_page (st : PipeBuf) (bs : List byte) :
    pipe_write_room st (bs.length : Int) = true →
    (pipe_append st bs).2 ≤ PIPE_BUF := by
  intro h
  obtain ⟨q, used⟩ := st
  cases q with
  | nil =>
    simp only [pipe_write_room, decide_eq_true_eq] at h
    simp only [pipe_append]
    exact h
  | cons b q' =>
    simp only [pipe_write_room, decide_eq_true_eq] at h
    simp only [pipe_append]
    omega

/-- A READ DOES NOT GIVE ROOM BACK: `anon_pipe_read` keeps `offset + len`
(:350-351).  After a 2-byte write and a 1-byte read one byte is queued and
a byte count says 4095 are free — yet `anon_pipe_write`'s merge test is
`offset 1 + len 1 + 4095 <= PAGE_SIZE` (:482-483), which fails, so Linux
puts those 4095 bytes on a second page and the one-slot model refuses. -/
theorem pipe_room_after_read_not_returned :
    pipe_write_room
      (pipe_consume (pipe_append ([], 0) [Z_to_bv 8 0x41, Z_to_bv 8 0x42]) 1)
      (PIPE_BUF - 1) = false := by decide

/-- The same state admits 4094 bytes: `1 + 1 + 4094 <= PAGE_SIZE` passes
`anon_pipe_write`'s merge test (:482-483), so the model's mark is exact, not merely
conservative. -/
theorem pipe_room_after_read_exact :
    pipe_write_room
      (pipe_consume (pipe_append ([], 0) [Z_to_bv 8 0x41, Z_to_bv 8 0x42]) 1)
      (PIPE_BUF - 2) = true := by decide

/-- The mark is untouched by any read, for every queue and count
(`anon_pipe_read`, :350-351, moves `offset` and `len` in opposite
directions). -/
theorem pipe_consume_keeps_mark (st : PipeBuf) (k : Nat) :
    (pipe_consume st k).2 = st.2 := rfl

/-- THE QUEUE IS FIFO.  A second write lands BEHIND the first:
`anon_pipe_write` merges into the last buffer at `buf->offset + buf->len`
(:480, `copy_page_from_iter(buf->page, offset, chars, from)` :488), and
`anon_pipe_read` copies from `buf->offset` (:343), the front.  A port
that prepended would read the second write first; every other pin here
appends into an EMPTY queue, where the two orders coincide. -/
theorem pipe_append_is_fifo :
    (pipe_append (pipe_append ([], 0) [Z_to_bv 8 0x41]) [Z_to_bv 8 0x42]).1
      = [Z_to_bv 8 0x41, Z_to_bv 8 0x42] ∧
    (pipe_append (pipe_append ([], 0) [Z_to_bv 8 0x41]) [Z_to_bv 8 0x42]).1
      ≠ [Z_to_bv 8 0x42, Z_to_bv 8 0x41] := by decide

/-- A read consumes from the FRONT: after `"AB"` is written and one byte
read, `"B"` remains — `anon_pipe_read` advances `buf->offset` by what it
copied (:350-351), it never trims `buf->len` from the back.  The room
pins above read only the mark of this state, which a back-trimming port
leaves the same. -/
theorem pipe_consume_takes_the_front :
    (pipe_consume (pipe_append ([], 0) [Z_to_bv 8 0x41, Z_to_bv 8 0x42]) 1).1
      = [Z_to_bv 8 0x42] ∧
    (pipe_consume (pipe_append ([], 0) [Z_to_bv 8 0x41, Z_to_bv 8 0x42]) 1).1
      ≠ [Z_to_bv 8 0x41] := by decide

/-- What a read of `n` delivers: the front `n` bytes (`anon_pipe_read`
clamps `chars` to `total_len`, fs/pipe.c:327-334, Linux v6.18.46, and
copies that many at :343); the whole queue when `n` exceeds it (`chars` is then the
buffer's own `len`, the copy empties the queue and the loop leaves
through `if (ret) break;` at :372-373 with the short count); and nothing
for a negative `n`, which no caller passes.  A read is this pair with
`pipe_consume`: `pipe_take` leaves the queue as it was. -/
theorem pipe_take_is_the_front_prefix :
    pipe_take [Z_to_bv 8 0x41, Z_to_bv 8 0x42] 1 = [Z_to_bv 8 0x41] ∧
    pipe_take [Z_to_bv 8 0x41, Z_to_bv 8 0x42] 5 = [Z_to_bv 8 0x41, Z_to_bv 8 0x42] ∧
    pipe_take [Z_to_bv 8 0x41, Z_to_bv 8 0x42] (-5) = [] ∧
    pipe_take [Z_to_bv 8 0x41, Z_to_bv 8 0x42] 1 ≠ [Z_to_bv 8 0x42] := by decide

/-- A FULL DRAIN RELEASES THE SLOT: once `buf->len` reaches 0,
`anon_pipe_read` runs `pipe_update_tail` (:359-362), so the next write
starts a fresh page and `PIPE_BUF` bytes fit again, whatever the drained
page's mark was. -/
theorem pipe_room_after_drain (u : Int) (bs : List byte) :
    pipe_write_room (pipe_consume (pipe_append ([], u) bs) bs.length) PIPE_BUF
      = true := by
  simp only [pipe_append, pipe_consume, List.drop_length, pipe_write_room,
    decide_eq_true_eq]
  exact Int.le_refl _

/-! ## The side table: ids and bindings -/

/-- Ids count creations: the empty table mints 0, one pipe later 1, a
rebinding of pipe 0 does not mint, and a second pipe gets 2.  The last
conjunct separates "count" from "lowest free" and "highest plus one": a
table holding only id 7 mints 1, not 0 and not 8.  Linux frees a closed
pipe's inode and reuses nothing a program can name (the argument is on
Rocq's `pipe_new_id`); an id handed out twice would let a fresh pipe
inherit a dead one's bytes. -/
theorem pipe_new_id_counts_creations :
    pipe_new_id [] = Z_to_bv 64 0 ∧
    pipe_new_id (pipe_insert [] (Z_to_bv 64 0) ([], 0)) = Z_to_bv 64 1 ∧
    pipe_new_id (pipe_insert (pipe_insert [] (Z_to_bv 64 0) ([], 0))
                   (Z_to_bv 64 0) ([Z_to_bv 8 1], 1)) = Z_to_bv 64 1 ∧
    pipe_new_id (pipe_insert (pipe_insert [] (Z_to_bv 64 0) ([], 0))
                   (Z_to_bv 64 1) ([], 0)) = Z_to_bv 64 2 ∧
    pipe_new_id [(Z_to_bv 64 7, ([], 0))] = Z_to_bv 64 1 := by
  decide

/-- Closing ends never removes a table entry: `fd_remove` is what `close`
does to `fdst_table`, and `fdst_pipes` is not read by it. -/
theorem pipe_table_survives_fd_remove (m : Model) (fd : word) :
    m_pipes (with_fds (fd_remove (m_fds m) fd) m) = m_pipes m := rfl

/-- The binding `pipe_insert` makes is the one `pipe_lookup` finds, the
first binding wins when a table carries two, and an id nothing bound
answers `none`. -/
theorem pipe_lookup_insert (ps : List (word × PipeBuf)) (id : word) (st : PipeBuf) :
    pipe_lookup (pipe_insert ps id st) id = some st := by
  simp only [pipe_insert, pipe_lookup, bv_eqb, beq_self_eq_true, ↓reduceIte]

theorem pipe_lookup_first_match :
    pipe_lookup [(Z_to_bv 64 0, ([Z_to_bv 8 1], 1)), (Z_to_bv 64 0, ([], 0))]
      (Z_to_bv 64 0) = some ([Z_to_bv 8 1], 1) ∧
    pipe_lookup [(Z_to_bv 64 0, ([], 0))] (Z_to_bv 64 1) = none :=
  ⟨rfl, rfl⟩

/-- WHY `PipeBuf` IS AN `abbrev`, AND WHAT BREAKS IF IT STOPS BEING ONE.
The arms that read a pipe match on `pipe_lookup (m_pipes m) id`, and
`sys_norm` opens that on a literal table by REWRITING with `pipe_lookup`'s
own equation lemma, the way `Cases/Fs/Namei.lean` registers
`fs_lookup.eq_2` for the file table — not by unfolding the name, which
`pipe_lookup_insert` above does and which a `def` never blocked.  The
rewrite assigns the lemma's `st : PipeBuf` pattern variable a pair whose
inferred type is `List byte × Int`, and `simp` checks that assignment at
a transparency that unfolds an `abbrev` and not a `def` (the docstring on
`PipeBuf` in `State/Fd.lean` names the Lean 4.34 source); Rocq's
`Definition PipeBuf` is transparent, so the twin has to be.  This proof
uses only that equation lemma, so it closes exactly while `PipeBuf` is
reducible: with `def` in its place `simp only` makes no progress and
reports the application type mismatch (checked in a scratch build of this
tree with the word changed back).  `pipe_lookup_first_match` above does
not guard this — `rfl` decides at default transparency, where a `def`
unfolds too. -/
theorem pipe_lookup_literal_by_equation_lemma :
    pipe_lookup [(Z_to_bv 64 0, ([Z_to_bv 8 1], 1)), (Z_to_bv 64 1, ([], 0))]
      (Z_to_bv 64 0) = some ([Z_to_bv 8 1], 1) := by
  simp only [pipe_lookup.eq_2, bv_eqb, beq_self_eq_true, ↓reduceIte]

/-! ## `pipe_end_live`: the counters `get_pipe_inode` sets and `pipe_release` keeps

For a `pipe2` pipe the counters start at one each: `get_pipe_inode` sets
`pipe->readers = pipe->writers = 1` (fs/pipe.c:902, Linux v6.18.46,
commit 1f99e9ab748f) and the two files come from `alloc_file_pseudo` /
`alloc_file_clone` (:944, :956), which never call `->open`, so
`fifo_open` (:1121) — the FIFO and by-path re-open path, which the model
never takes — does not run.  `pipe_release` lowers each counter by the
file's `f_mode` (:730-733). -/

/-- With both ends of pipe 0 open, each direction is live; `fd_remove` of
the write end is what `pipe_release` lowering `pipe->writers` by
`FMODE_WRITE` (:730-733) looks like here — the reader stays, the writer
is gone. -/
theorem pipe_end_live_both_ends :
    let fds : List (word × FdEntry) :=
      [ (Z_to_bv 64 0, .FdChannel (Z_to_bv 64 0)),
        (Z_to_bv 64 3, .FdPipe (Z_to_bv 64 0) false),
        (Z_to_bv 64 4, .FdPipe (Z_to_bv 64 0) true) ]
    pipe_end_live fds (Z_to_bv 64 0) true = true ∧
    pipe_end_live fds (Z_to_bv 64 0) false = true ∧
    pipe_end_live (fd_remove fds (Z_to_bv 64 4)) (Z_to_bv 64 0) true = false ∧
    pipe_end_live (fd_remove fds (Z_to_bv 64 4)) (Z_to_bv 64 0) false = true := by
  decide

/-- What is NOT a writer of pipe 0: its own read end (`pipe_release`
lowers `pipe->readers` for an `FMODE_READ` file and `pipe->writers` only
for `FMODE_WRITE`, :730-733, so a read end never counts as a writer), the
write end of another pipe, and any non-pipe descriptor whatever its fd
number. -/
theorem pipe_end_live_negatives :
    pipe_end_live [(Z_to_bv 64 3, .FdPipe (Z_to_bv 64 0) false)] (Z_to_bv 64 0) true
      = false ∧
    pipe_end_live [(Z_to_bv 64 4, .FdPipe (Z_to_bv 64 1) true)] (Z_to_bv 64 0) true
      = false ∧
    pipe_end_live [ (Z_to_bv 64 4, .FdFileW [] (Z_to_bv 64 0)),
                    (Z_to_bv 64 5, .FdDevNull true true),
                    (Z_to_bv 64 6, .FdChannel (Z_to_bv 64 1)) ]
      (Z_to_bv 64 0) true = false := by
  decide

/-- The random device is neither pipe end: `memory_open` installs
`urandom_fops` for its node (drivers/char/mem.c:701, :720), and on the
paths the model takes only a pipe file's `pipe_release` (fs/pipe.c:730-733)
moves `pipe->readers` and `pipe->writers` after `get_pipe_inode` (:902)
set them — `fifo_open` (:1167, :1193) also raises them, on the by-path
re-open the section header above excludes.  A device listed
before a live writer does not hide it either: the walk continues past
it.
kernel: fs/pipe.c:get_pipe_inode,pipe_release; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem pipe_end_live_skips_urandom :
    pipe_end_live [(Z_to_bv 64 3, .FdPipe (Z_to_bv 64 0) false), (Z_to_bv 64 5, .FdUrandom)]
      (Z_to_bv 64 0) true = false ∧
    pipe_end_live [(Z_to_bv 64 5, .FdUrandom), (Z_to_bv 64 4, .FdPipe (Z_to_bv 64 0) true)]
      (Z_to_bv 64 0) true = true := by
  decide

/-! ## `pipe_fd_bytes`: what `do_pipe2` copies out -/

/-- `__do_pipe_flags` sets `fd[0] = fdr`, `fd[1] = fdw` (:1005-1006) and
`do_pipe2` copies the `int fildes[2]` out in one `copy_to_user` (:1040):
fds 3 and 4 become
these eight little-endian bytes, read end first, and not the other
order. -/
theorem pipe_fd_bytes_layout :
    pipe_fd_bytes (Z_to_bv 64 3) (Z_to_bv 64 4)
      = [ Z_to_bv 8 3, Z_to_bv 8 0, Z_to_bv 8 0, Z_to_bv 8 0,
          Z_to_bv 8 4, Z_to_bv 8 0, Z_to_bv 8 0, Z_to_bv 8 0 ] ∧
    pipe_fd_bytes (Z_to_bv 64 3) (Z_to_bv 64 4)
      ≠ pipe_fd_bytes (Z_to_bv 64 4) (Z_to_bv 64 3) := by
  decide

/-- `le32_bytes` is the low `int` of the word, least significant byte
first, and only the low 32 bits: the high half of an fd word is not
copied out, and the pair is `sizeof(int[2])` bytes. -/
theorem le32_bytes_little_endian :
    le32_bytes (Z_to_bv 64 0x01020304)
      = [ Z_to_bv 8 4, Z_to_bv 8 3, Z_to_bv 8 2, Z_to_bv 8 1 ] ∧
    le32_bytes (Z_to_bv 64 0xff00000001020304)
      = le32_bytes (Z_to_bv 64 0x01020304) ∧
    (pipe_fd_bytes (Z_to_bv 64 3) (Z_to_bv 64 4)).length = 8 := by
  decide

/-! ## Stream and network reads — ticket A9 (`stream_take_z`, `net_take`,
`net_take_z`, `net_rest`)

Kernel citations in this section are Linux v6.18.46, commit
1f99e9ab748f, read in the named file and function.  The laws the pins go
through (`stream_take_z_eq`, `net_take_z_eq` and the `net_take` equations)
are the Rocq lemma twins in `StreamLaws.lean`. -/

/-! ### Stdin reads through the digit-indexed take

Each pair states a kernel behaviour, positive and negative.  The counts
2, 3 and 5 are these pins' own, and their `positive` spellings (2 is
`xO xH`, 3 is `xI xH`, 5 is `xI (xO xH)`) are informational: the
positive-count pins open with `stream_take_z_eq` and compute through
`stream_take`, so the digit recursion is exercised by
`StreamLaws.stream_take_pos_eq`, not here. -/

/-- A read asking for more than the input holds delivers what is there and
then finds end of input: fs/pipe.c `anon_pipe_read` (Linux v6.18.46) copies
`chars = buf->len` when the buffer holds fewer bytes than `total_len` (line
323)
and returns with `ret` short once the pipe is empty. -/
theorem read_short_then_eof (b c : byte) :
    stream_take_z (ICons b (ICons c IEof)) 5 = ([b, c], IEof) := by
  rw [stream_take_z_eq]
  simp only [Int.toNat, stream_take_cons, stream_take_eof]

/-- A read past the end of input cannot deliver a byte the input never
held: `anon_pipe_read` copies only `buf->len` bytes of a buffer (line
323); nothing is invented past the last written one. -/
theorem read_short_invented_byte_rejected (b c : byte) :
    stream_take_z (ICons b (ICons c IEof)) 3 ≠ ([b, c, c], IEof) := by
  rw [stream_take_z_eq]
  simp only [Int.toNat, stream_take_cons, stream_take_eof]
  intro h
  have hlen := congrArg (fun r : List byte × InputStream => r.1.length) h
  simp only [List.length_cons, List.length_nil] at hlen
  omega

/-- A read asking for fewer bytes than the input holds leaves the rest for
the next read: `anon_pipe_read` clamps `chars = total_len` (line 333) and
advances `buf->offset` by only those bytes, so the unread tail stays in
the pipe. -/
theorem read_leaves_unread_tail (b c d : byte) :
    stream_take_z (ICons b (ICons c (ICons d IEof))) 2 = ([b, c], ICons d IEof) := by
  rw [stream_take_z_eq]
  simp only [Int.toNat, stream_take_cons, stream_take_zero]

/-- The unread tail is not dropped: the next read still sees `d`, not end of
input (`anon_pipe_read`, line 333). -/
theorem read_dropped_tail_rejected (b c d : byte) :
    stream_take_z (ICons b (ICons c (ICons d IEof))) 2 ≠ ([b, c], IEof) := by
  rw [read_leaves_unread_tail]
  intro h
  exact ICons_ne_IEof d IEof (congrArg Prod.snd h)

/-- A zero-length read consumes nothing and delivers nothing: fs/pipe.c
`anon_pipe_read` (Linux v6.18.46) returns 0 before touching the pipe when
`total_len == 0` (line 278), and fs/read_write.c `vfs_read` (line 566,
Linux v6.18.46) clamps every count
to `MAX_RW_COUNT`, so the count the model is handed is never negative. -/
theorem read_zero_length (s : InputStream) : stream_take_z s 0 = ([], s) := rfl

/-- A zero-length read does not advance the input: the one byte is still
there for the following read, which does not find end of input
(`anon_pipe_read`, line 278).  Stated on a finite input on purpose: an
unbounded constant input is its own tail, so it could not tell. -/
theorem read_zero_length_advance_rejected (b : byte) :
    stream_take_z (ICons b IEof) 0 ≠ ([], IEof) := by
  rw [read_zero_length]
  intro h
  exact ICons_ne_IEof b IEof (congrArg Prod.snd h)

/-! ### What a peer's script lets a read deliver -/

/-- Every read after a FIN delivers 0 and the FIN stays: net/ipv4/tcp_input.c
`tcp_fin` (Linux v6.18.46) sets `RCV_SHUTDOWN` and `SOCK_DONE` (lines
4726–4727), so net/ipv4/tcp.c `tcp_recvmsg_locked` (Linux v6.18.46) breaks
on `SOCK_DONE` (line 2741) with `copied` still 0, at every later read —
and no modeled trace clears them.  On a socket that has taken a FIN and
is still open, the one function clearing both is net/ipv4/tcp.c
`tcp_disconnect` (Linux v6.18.46, lines 3390–3391), reached only from
`connect`: net/ipv4/af_inet.c `__inet_stream_connect` (Linux v6.18.46)
calls it for `AF_UNSPEC` (lines 646–648) and for a connection that reached
`TCP_CLOSE` under it (lines 721–722, then 734–738).  `connect_spec`
(Sys/Net/Socket.lean) answers `unmodeled` both for `AF_UNSPEC` on a
connected socket (pinned by `connect_accepted_af_unspec_declines`,
Checks/Cases/Net/Socket.lean) and for the connect attempt itself, so no
modeled socket is ever `SS_CONNECTING`: neither route is a modeled trace.
The other two resets of `SOCK_DONE` never see a taken FIN: net/ipv4/tcp_output.c
`tcp_connect_init` (Linux v6.18.46, line 4090) runs for a socket
`__inet_stream_connect` finds `SS_UNCONNECTED` and in `TCP_CLOSE` (lines
668–671), a pair a socket that took a FIN regains only through
`tcp_disconnect`, and net/core/sock.c `sk_clone_lock` (Linux v6.18.46,
line 2518) initialises a newborn child.  This stops holding when
`connect_spec` models `AF_UNSPEC` on a connected socket: that arm then
owes the script's terminal a reset. -/
theorem fin_reads_zero_forever (n : Int) : net_take_z NFin n = ([], NFin) := by
  rw [net_take_z_eq, net_take_fin]

/-- No byte follows a FIN.  Bytes queued BEFORE the FIN stay deliverable
(`tcp_fin` purges only the out-of-order queue, net/ipv4/tcp_input.c line
4772); what cannot happen is a byte AFTER it: net/ipv4/tcp_input.c
`tcp_rcv_state_process` (Linux v6.18.46) step 7 drops in-sequence data in
`TCP_CLOSE_WAIT`
without queueing it (lines 7165–7174), and in `TCP_FIN_WAIT1`/`2` answers
data past the FIN with `tcp_reset` (lines 7183–7187). -/
theorem fin_then_byte_rejected (k : Nat) (b : byte) (bs : List byte) (r : NetStream) :
    net_take NFin k ≠ (b :: bs, r) := by
  rw [net_take_fin]
  intro h
  cases congrArg Prod.fst h

/-- Bytes the peer sent before resetting are delivered first: net/ipv4/tcp.c
`tcp_recvmsg_locked` (Linux v6.18.46) walks `sk_receive_queue` (line 2703)
before it consults `sk_err` (line 2744), and net/ipv4/tcp_input.c
`tcp_done_with_error` (Linux v6.18.46) purges only the write queue (line
4669).  The reset
is still there for the following read to report. -/
theorem bytes_before_reset_delivered (b : byte) :
    net_take (NCons b NRst) 4 = ([b], NRst) := by
  rw [net_take_cons, net_take_rst]

/-- A reset is not softened into an orderly close: the read after the bytes
answers `-ECONNRESET` through include/net/sock.h `sock_error` (line 2496,
Linux v6.18.46, reached from `tcp_recvmsg_locked` line 2745), not 0. -/
theorem reset_softened_to_fin_rejected (b : byte) :
    net_take (NCons b NRst) 1 ≠ ([b], NFin) := by
  rw [net_take_cons, net_take_zero]
  intro h
  exact network_fin_ne_reset (congrArg Prod.snd h).symm

/-- A read of more than the peer sent delivers the bytes and then the
timeout, both halves of the digit recursion crossing the terminal:
`tcp_recvmsg_locked` copies `used = skb->len - offset` bytes of each
buffer (line 2794) and stops at the terminal with `copied` short. -/
theorem bytes_then_timeout (b c : byte) :
    net_take_z (NCons b (NCons c NTimedOut)) 5 = ([b, c], NTimedOut) := by
  rw [net_take_z_eq]
  simp only [Int.toNat, net_take_cons, net_take_timedout]

/-- A read across the FIN cannot deliver a byte the peer never sent
(`tcp_recvmsg_locked`, line 2794: only `skb->len` bytes of a buffer). -/
theorem net_invented_byte_rejected (b : byte) :
    net_take_z (NCons b NFin) 2 ≠ ([b, b], NFin) := by
  rw [net_take_z_eq]
  simp only [Int.toNat, net_take_cons, net_take_fin]
  intro h
  have hlen := congrArg (fun r : List byte × NetStream => r.1.length) h
  simp only [List.length_cons, List.length_nil] at hlen
  omega

/-- A short read leaves the unread bytes queued: `tcp_recvmsg_locked` clamps
`used = len` (line 2796) and advances `copied_seq` by only that much, so
the next read sees `c`. -/
theorem net_read_leaves_unread_tail (b c : byte) :
    net_take (NCons b (NCons c NFin)) 1 = ([b], NCons c NFin) := by
  rw [net_take_cons, net_take_zero]

/-- The unread byte is not dropped into the FIN (`tcp_recvmsg_locked`,
line 2796). -/
theorem net_dropped_tail_rejected (b c : byte) :
    net_take (NCons b (NCons c NFin)) 1 ≠ ([b], NFin) := by
  rw [net_read_leaves_unread_tail]
  intro h
  have h0 := congrArg (fun q : NetStream => q.cell_at 0) (congrArg Prod.snd h)
  cases h0

/-- A terminal is never consumed: a second read after the FIN finds the FIN
(`tcp_fin`, lines 4726–4727), so `net_rest` at a terminal is still ended. -/
theorem terminal_survives_read (s : NetStream) (k : Nat) (h : net_ended s = true) :
    net_ended (net_rest s k) = true := by
  unfold net_rest
  rw [net_take_ended s k h]
  exact h

/-- A read does not consume the FIN into a live script: whatever follows a
read after the FIN, it is not a byte (`tcp_fin`, lines 4726–4727;
`tcp_rcv_state_process`, lines 7165–7174). -/
theorem terminal_consumed_rejected (k : Nat) (b : byte) (r : NetStream) :
    net_rest NFin k ≠ NCons b r := by
  unfold net_rest
  rw [net_take_fin]
  intro h
  have h0 := congrArg (fun q : NetStream => q.cell_at 0) h
  cases h0

/-! ## The errno block (ticket A1) -/

/-- The errno-base.h names carry the numbers the header gives them
(include/uapi/asm-generic/errno-base.h:5-38, Linux v6.18.46, commit
1f99e9ab748f). -/
theorem errno_base_values :
    EPERM = 1 ∧ ENOENT = 2 ∧ ESRCH = 3 ∧ EINTR = 4 ∧ EBADF = 9 ∧ ECHILD = 10
    ∧ EAGAIN = 11 ∧ ENOMEM = 12 ∧ EACCES = 13 ∧ EFAULT = 14 ∧ EBUSY = 16
    ∧ EEXIST = 17 ∧ ENOTDIR = 20 ∧ EISDIR = 21 ∧ EINVAL = 22 ∧ ENFILE = 23
    ∧ EMFILE = 24 ∧ ENOTTY = 25 ∧ ESPIPE = 29 ∧ EROFS = 30 ∧ EPIPE = 32
    ∧ ERANGE = 34 := by decide

/-- The errno.h names carry the numbers the header gives them
(include/uapi/asm-generic/errno.h:8,20,71-94, Linux v6.18.46, commit
1f99e9ab748f). -/
theorem errno_extended_values :
    ENAMETOOLONG = 36 ∧ ENOTEMPTY = 39 ∧ ENOTSOCK = 88 ∧ EMSGSIZE = 90
    ∧ ENOPROTOOPT = 92 ∧ EPROTONOSUPPORT = 93 ∧ ESOCKTNOSUPPORT = 94
    ∧ EOPNOTSUPP = 95 ∧ EAFNOSUPPORT = 97 ∧ EADDRINUSE = 98 ∧ ECONNRESET = 104
    ∧ EISCONN = 106 ∧ ENOTCONN = 107 ∧ ETIMEDOUT = 110 ∧ ECONNREFUSED = 111 := by
  decide

/-- The mistake: reading an ARCHITECTURE'S errno table instead of the
generic one riscv64 inherits.  Four architectures renumber this block
(powerpc's own errno.h touches only `EDEADLOCK`): each of the four moves
every socket errno, `ENAMETOOLONG` and `ENOTEMPTY`, and alpha alone also
moves `EAGAIN` — `EAGAIN` is 35 and `ENOTSOCK` 38 on alpha
(arch/alpha/include/uapi/asm/errno.h), `ENOTSOCK` is 38 on sparc
(arch/sparc/include/uapi/asm/errno.h), `ENOTSOCK` is 95 and `ETIMEDOUT`
145 on mips (arch/mips/include/uapi/asm/errno.h), `ENOTSOCK` is 216 and
`ENAMETOOLONG` 248 on parisc (arch/parisc/include/uapi/asm/errno.h), all
Linux v6.18.46.  A model built from any of those would decode a riscv64
`-ETIMEDOUT` as a different failure. -/
theorem errnos_are_not_an_arch_table :
    EAGAIN ≠ 35 ∧ ENOTSOCK ≠ 38 ∧ ENOTSOCK ≠ 95 ∧ ENOTSOCK ≠ 216
    ∧ ETIMEDOUT ≠ 60 ∧ ETIMEDOUT ≠ 145 ∧ ETIMEDOUT ≠ 238
    ∧ EOPNOTSUPP ≠ 45 ∧ EOPNOTSUPP ≠ 122 ∧ EOPNOTSUPP ≠ 223
    ∧ ENAMETOOLONG ≠ 63 ∧ ENAMETOOLONG ≠ 78 ∧ ENAMETOOLONG ≠ 248
    ∧ ENOTEMPTY ≠ 66 ∧ ENOTEMPTY ≠ 93 ∧ ENOTEMPTY ≠ 247 := by decide

/-- The values are pairwise distinct, so a transcription that gave two
names one number — the neighbours `ENOTDIR`/`EISDIR` at 20/21, or
`EPROTONOSUPPORT`/`ESOCKTNOSUPPORT` at 93/94 — is refused; every one of
them is a distinct `#define` in the two headers cited above. -/
theorem errnos_are_distinct :
    [EPERM, ENOENT, ESRCH, EINTR, EBADF, ECHILD, EAGAIN, ENOMEM, EACCES, EFAULT,
     EBUSY, EEXIST, ENOTDIR, EISDIR, EINVAL, ENFILE, EMFILE, ENOTTY, ESPIPE, EROFS,
     EPIPE, ERANGE, ENAMETOOLONG, ENOTEMPTY, ENOTSOCK, EMSGSIZE, ENOPROTOOPT,
     EPROTONOSUPPORT, ESOCKTNOSUPPORT, EOPNOTSUPP, EAFNOSUPPORT, EADDRINUSE,
     ECONNRESET, EISCONN, ENOTCONN, ETIMEDOUT, ECONNREFUSED].Nodup := by decide

/-- A failing syscall's a0 is `-errno` in two's complement — the band
`[2^64 - 4095, 2^64 - 1]` that `MAX_ERRNO` and `IS_ERR_VALUE` (include/linux/err.h:18,28,
Linux v6.18.46, commit 1f99e9ab748f) reserves — so the largest and smallest
values here land inside it, and the mistake of handing back the positive
number, which userspace would read as a success of 1 byte or of fd 1, is
refused. -/
theorem errno_ret_encodes_the_block :
    bv_unsigned (errno_ret EPERM) = 2 ^ 64 - 1
    ∧ bv_unsigned (errno_ret ECONNREFUSED) = 2 ^ 64 - 111
    ∧ 2 ^ 64 - 4095 ≤ bv_unsigned (errno_ret ECONNREFUSED)
    ∧ bv_unsigned (errno_ret EPERM) ≠ 1 := by decide

/-! ## Descriptor allocation — ticket A7 (`alloc_fd`, `alloc_fd2`)

Each table below is keyed by the descriptors it holds; the entry kind does
not enter the kernel's bitmap scan (`alloc_fd_kind_blind`), so `FdChannel`
stands in for every kind elsewhere. -/

/-- `alloc_fd2` answers at most 8193: `alloc_fd`'s 4096 plus one, plus a
second scan of 4096. -/
theorem alloc_fd2_le (fds : List (word × FdEntry)) : bv_unsigned (alloc_fd2 fds) ≤ 8193 := by
  have h1 := alloc_fd_le fds
  have h1' : (alloc_fd fds).toNat + 1 < 2 ^ 64 := by
    simp only [bv_unsigned] at h1
    omega
  have hone : (1 : word).toNat = 1 := by decide
  have hu : bv_unsigned (alloc_fd fds + 1) = bv_unsigned (alloc_fd fds) + 1 := by
    simp only [bv_unsigned]
    rw [BitVec.toNat_add, hone, Nat.mod_eq_of_lt h1']
    omega
  have h := alloc_fd_aux_le 4096 fds (alloc_fd fds + 1) (by rw [hu]; omega)
  rw [hu] at h
  unfold alloc_fd2
  omega

/-- A table holding exactly the descriptors listed. -/
def alloc_fd_table (fds : List Int) : List (word × FdEntry) :=
  fds.map (fun k => (Z_to_bv 64 k, FdEntry.FdChannel (Z_to_bv 64 k)))

/-- With 0, 1, 2 and 4 live, `alloc_fd` answers 3 — the first clear bit of
`open_fds` from 0, not the one after the highest live descriptor (fs/file.c
`find_next_fd`, Linux v6.18.46). -/
theorem alloc_fd_hole_is_3 :
    alloc_fd (alloc_fd_table [0, 1, 2, 4]) = Z_to_bv 64 3 := by decide

/-- ... and NOT 5, which a "past the highest" allocator would say. -/
theorem alloc_fd_hole_not_5 :
    alloc_fd (alloc_fd_table [0, 1, 2, 4]) ≠ Z_to_bv 64 5 := by decide

/-- A fresh process's first open gets 3: the three standard descriptors are
live in `init_model`, and `alloc_fd(0, nofile, flags)` takes the first clear
bit above them (fs/file.c `__get_unused_fd_flags`, Linux v6.18.46). -/
theorem alloc_fd_init_model_is_3 (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    alloc_fd (m_fds (init_model reserved brk0 mbase sp lim inp)) = Z_to_bv 64 3 := rfl

/-- ... and NOT 2, a live descriptor: `__set_open_fd` (fs/file.c, Linux
v6.18.46) marks each taken bit, so the scan never reissues one. -/
theorem alloc_fd_init_model_not_2 (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    alloc_fd (m_fds (init_model reserved brk0 mbase sp lim inp)) ≠ Z_to_bv 64 2 := by
  rw [alloc_fd_init_model_is_3]
  decide

/-- After `close(1)` the next open returns 1: `__put_unused_fd` lowered
`next_fd` back to 1, so the scan reuses it (fs/file.c, Linux v6.18.46). -/
theorem alloc_fd_reuses_closed_1 :
    alloc_fd (alloc_fd_table [0, 2]) = Z_to_bv 64 1 := by decide

/-- ... and NOT 3, which a never-reuse allocator would say. -/
theorem alloc_fd_reuses_closed_1_not_3 :
    alloc_fd (alloc_fd_table [0, 2]) ≠ Z_to_bv 64 3 := by decide

/-- The empty table answers 0: `__get_unused_fd_flags` passes `start = 0`
to `alloc_fd` (fs/file.c, Linux v6.18.46). -/
theorem alloc_fd_empty_is_0 : alloc_fd (alloc_fd_table []) = Z_to_bv 64 0 := by decide

/-- ... and NOT 1: an allocator that started above 0 would never hand out
descriptor 0, which a process that closed stdin gets back. -/
theorem alloc_fd_empty_not_1 : alloc_fd (alloc_fd_table []) ≠ Z_to_bv 64 1 := by decide

/-- The bitmap has no order: the table `[4, 2, 1, 0]` answers what
`[0, 1, 2, 4]` does, not the first descriptor it happens to list
(fs/file.c `find_next_fd` scans `open_fds` by position, Linux v6.18.46). -/
theorem alloc_fd_order_blind :
    alloc_fd (alloc_fd_table [4, 2, 1, 0]) = Z_to_bv 64 3 := by decide

/-- ... and NOT 5, the answer of a "past the first listed" allocator. -/
theorem alloc_fd_order_blind_not_5 :
    alloc_fd (alloc_fd_table [4, 2, 1, 0]) ≠ Z_to_bv 64 5 := by decide

/-- THE FUEL BOUNDARY, the one place the model's answer is not the
kernel's.  `alloc_fd` is `alloc_fd_aux` from 0 with fuel 4096, and the
`0` arm of `alloc_fd_aux` answers the CURRENT candidate whether or not
the table holds it.  Stated at fuel 3 so the kernel can evaluate it — the
decision is the arm's, not the fuel's value, which the first conjunct
restates and `alloc_fd_le` bounds only from above: with 0, 1, 2 held the
exhausted scan lands on 3, which is free, exactly what `find_next_fd`
(fs/file.c, Linux v6.18.46) answers; with 0, 1, 2, 3 held it still
answers 3, which is HELD.  Linux has no such ceiling — fs/file.c's
`alloc_fd` refuses only at `fd >= end`, the `end` that
`get_unused_fd_flags` passes as `rlimit(RLIMIT_NOFILE)`, or when
`expand_files` will not grow the table past `sysctl_nr_open` — so a
caller should test the answer's freeness and decline when it fails.
Today every `lowest_fd` caller falls to an errno there instead and only
the socketpair arm declines; bugs/fd-allocation-ignores-rlimit-nofile.md
carries what that costs above 4096 live descriptors. -/
theorem alloc_fd_aux_exhausted_fuel_answers_the_candidate (fds : List (word × FdEntry)) :
    alloc_fd fds = alloc_fd_aux fds (Z_to_bv 64 0) 4096 ∧
    alloc_fd_aux (alloc_fd_table [0, 1, 2]) (Z_to_bv 64 0) 3 = Z_to_bv 64 3 ∧
    fd_lookup (alloc_fd_table [0, 1, 2]) (Z_to_bv 64 3) = none ∧
    alloc_fd_aux (alloc_fd_table [0, 1, 2, 3]) (Z_to_bv 64 0) 3 = Z_to_bv 64 3 ∧
    fd_lookup (alloc_fd_table [0, 1, 2, 3]) (Z_to_bv 64 3) ≠ none :=
  ⟨rfl, by decide, by decide, by decide, by decide⟩

/-- What `alloc_fd` answers never reads as an error-encoded return: it is
at most 4096 (`alloc_fd_le`) and the errno window is the top 4095 values
of the word.  Rocq states the same as `alloc_fd_not_error_b`
(Checks/Sys/Fs/Open.v); here it is the fact that lets an arm hand the
descriptor back in `a0` without an errno check. -/
theorem alloc_fd_never_reads_as_errno (fds : List (word × FdEntry)) :
    addr_is_error_b (alloc_fd fds) = false := by
  have h := alloc_fd_le fds
  unfold addr_is_error_b two_pow_64
  exact decide_eq_false (by omega)

/-- The pair a `pipe2`/`socketpair` takes from a fresh process is (3, 4):
the second `get_unused_fd_flags` sees the first answer already set in
`open_fds` (fs/pipe.c `__do_pipe_flags`, net/socket.c `__sys_socketpair`,
Linux v6.18.46). -/
theorem alloc_fd2_init_is_4 :
    alloc_fd2 (alloc_fd_table [0, 1, 2]) = Z_to_bv 64 4 := by decide

/-- ... and NEVER the same descriptor twice. -/
theorem alloc_fd2_init_not_3 :
    alloc_fd2 (alloc_fd_table [0, 1, 2]) ≠ Z_to_bv 64 3 := by decide

/-- With 4 live above the hole at 3, the pair is (3, 5): the second scan
skips both the first answer and the live 4. -/
theorem alloc_fd2_skips_live_4 :
    alloc_fd (alloc_fd_table [0, 1, 2, 4]) = Z_to_bv 64 3 ∧
    alloc_fd2 (alloc_fd_table [0, 1, 2, 4]) = Z_to_bv 64 5 := by decide

/-- ... and NOT 4, which a second scan that ignored the bitmap would say. -/
theorem alloc_fd2_skips_live_4_not_4 :
    alloc_fd2 (alloc_fd_table [0, 1, 2, 4]) ≠ Z_to_bv 64 4 := by decide

/-- The entry kind does not enter the scan: `open_fds` is a bitmap of
descriptors, not of what they name (`__set_open_fd` and `find_next_fd`,
fs/file.c, Linux v6.18.46).  A directory, a pipe end and /dev/null at
0, 1, 2 answer 3 exactly as three channels do. -/
theorem alloc_fd_kind_blind :
    alloc_fd [ (Z_to_bv 64 0, FdEntry.FdDir),
               (Z_to_bv 64 1, FdEntry.FdPipe (Z_to_bv 64 7) true),
               (Z_to_bv 64 2, FdEntry.FdDevNull true false) ] = Z_to_bv 64 3 := by decide

/-! ## The user-memory readers (ticket A3) -/

/-- `bs` laid out from address `lo`, nothing else mapped. -/
def pin_mem (lo : Nat) (bs : List byte) : word → Option byte :=
  fun a => if lo ≤ a.toNat then bs[a.toNat - lo]? else none

/-- `n` non-NUL bytes (`'a'`) from address `lo`, then a NUL, nothing
else mapped. -/
def pin_run (lo n : Nat) : word → Option byte :=
  fun a =>
    if lo ≤ a.toNat then
      if a.toNat < lo + n then some 0x61#8
      else if a.toNat = lo + n then some 0#8
      else none
    else none

/-- `pin_run` read through `read_cstr_aux`, in closed form: from offset
`i` of the run, the string is the remaining `n - i` content bytes when the
NUL lies within the fuel, and too long otherwise.  The PATH_MAX pins below
close through this rather than by evaluating a 4096-step walk, which
Lean's kernel cannot do within its recursion budget. -/
theorem read_cstr_aux_run (lo n : Nat) (hn : lo + n < 2 ^ 64) (k : Nat) :
    ∀ i, i ≤ n →
      read_cstr_aux (pin_run lo n) (BitVec.ofNat 64 (lo + i)) k
        = if n - i < k then CstrOk (List.replicate (n - i) 0x61#8) else CstrTooLong := by
  induction k with
  | zero =>
    intro i _
    simp only [read_cstr_aux, Nat.not_lt_zero, ↓reduceIte]
  | succ k ih =>
    intro i hi
    have hto : (BitVec.ofNat 64 (lo + i)).toNat = lo + i := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hstep : BitVec.ofNat 64 (lo + i) + 1 = BitVec.ofNat 64 (lo + (i + 1)) := by
      rw [← Nat.add_assoc, BitVec.ofNat_add (lo + i) 1]
      rfl
    have hlo : lo ≤ lo + i := Nat.le_add_right lo i
    simp only [read_cstr_aux, pin_run, hto, hlo, ↓reduceIte]
    by_cases hlt : lo + i < lo + n
    · have hne : bv_eqb 0x61#8 (Z_to_bv 8 0) = false := by decide
      simp only [hlt, ↓reduceIte, hne, Bool.false_eq_true, hstep]
      rw [ih (i + 1) (by omega)]
      by_cases hk : n - (i + 1) < k
      · have hk' : n - i < k + 1 := by omega
        have hrep : n - i = (n - (i + 1)) + 1 := by omega
        simp only [hk, hk', ↓reduceIte]
        rw [hrep, List.replicate_succ]
      · have hk' : ¬ (n - i < k + 1) := by omega
        simp only [hk, hk', ↓reduceIte]
    · have hi' : i = n := by omega
      subst hi'
      have hz : bv_eqb 0#8 (Z_to_bv 8 0) = true := by decide
      simp only [hlt, ↓reduceIte, hz, Nat.sub_self, List.replicate_zero, Nat.zero_lt_succ]

/-- **read_cstr, NUL unmapped answers the fault result.**  `"ab"` at
0x1000 with 0x1002 unmapped: `strncpy_from_user` faults before finding a
NUL and returns `-EFAULT` (lib/strncpy_from_user.c, `do_strncpy_from_user`,
v6.18.46), which is returned as `ERR_PTR(len)` (fs/namei.c,
`getname_flags`, v6.18.46). -/
theorem pin_read_cstr_unmapped_nul_faults :
    read_cstr (pin_mem 0x1000 [0x61#8, 0x62#8]) 0x1000#64 = CstrFault := by decide

/-- The fault is not reported as a too-long name: an unmapped byte is
`-EFAULT`, never `-ENAMETOOLONG`. -/
theorem pin_read_cstr_unmapped_nul_not_too_long :
    read_cstr (pin_mem 0x1000 [0x61#8, 0x62#8]) 0x1000#64 ≠ CstrTooLong := by decide

/-- With the NUL mapped, the same buffer is the string `"ab"`. -/
theorem pin_read_cstr_terminated_ok :
    read_cstr (pin_mem 0x1000 [0x61#8, 0x62#8, 0#8]) 0x1000#64
      = CstrOk [0x61#8, 0x62#8] := by decide

/-- The NUL is not part of the string. -/
theorem pin_read_cstr_terminated_excludes_nul :
    read_cstr (pin_mem 0x1000 [0x61#8, 0x62#8, 0#8]) 0x1000#64
      ≠ CstrOk [0x61#8, 0x62#8, 0#8] := by decide

/-- An unmapped byte at the START is a fault too: the walk does not skip. -/
theorem pin_read_cstr_unmapped_start_faults :
    read_cstr (pin_mem 0x1001 [0#8]) 0x1000#64 = CstrFault := by decide

/-- **The empty pathname is a name, not a failure.**  A NUL as the first
byte is the string `""`: `strncpy_from_user` returns 0 for it
(lib/strncpy_from_user.c, `do_strncpy_from_user`, v6.18.46), and
`getname_flags` turns THAT into `-ENOENT` unless `LOOKUP_EMPTY` is set,
on its first pass (fs/namei.c:157-171, `if (unlikely(len <= 0))` … `if
(!(flags & LOOKUP_EMPTY)) return ERR_PTR(-ENOENT)`, v6.18.46; the `!len`
test at :202 belongs to the PATH_MAX retry, which an empty name never
reaches) — a decision for the arm, which is why the reader answers
`CstrOk []` and neither failure. -/
theorem pin_read_cstr_empty_is_ok :
    read_cstr (pin_mem 0x1000 [0#8]) 0x1000#64 = CstrOk [] ∧
    read_cstr (pin_mem 0x1000 [0#8]) 0x1000#64 ≠ CstrFault ∧
    read_cstr (pin_mem 0x1000 [0#8]) 0x1000#64 ≠ CstrTooLong := by decide

/-- **The string stops at the FIRST NUL.**  `"a\0b"` is `"a"`:
`do_strncpy_from_user` returns at the first zero byte (`return res +
find_zero(data)`, lib/strncpy_from_user.c, v6.18.46), so the `b` is not
part of the name.  Whether the kernel READS it is a different question:
the aligned path loads a whole word and masks the bytes past the NUL
(:54-59), the copy-in ledger question
bugs/openat-getname-word-at-a-time.md records. -/
theorem pin_read_cstr_stops_at_first_nul :
    read_cstr (pin_mem 0x1000 [0x61#8, 0#8, 0x62#8]) 0x1000#64 = CstrOk [0x61#8] ∧
    read_cstr (pin_mem 0x1000 [0x61#8, 0#8, 0x62#8]) 0x1000#64
      ≠ CstrOk [0x61#8, 0#8, 0x62#8] := by decide

/-- **With the fuel exhausted, exactly the fuel is counted.**  A run of
content longer than the fuel records `fuel` bytes read, one per candidate,
and not one more: `strncpy_from_user(kname, filename, PATH_MAX)` reads
`count` bytes and returns `count` when no NUL turned up in them
(lib/strncpy_from_user.c, `do_strncpy_from_user`, `if (res >= count)
return res`, v6.18.46).  Stated at fuel 4 for the same reason the PATH_MAX
pins go through `read_cstr_aux_run`. -/
theorem pin_cstr_access_len_exhausted_counts_the_fuel :
    cstr_access_len_aux (pin_run 0x1000 8) 0x1000#64 4 = 4 ∧
    cstr_access_len_aux (pin_run 0x1000 8) 0x1000#64 4 ≠ 5 := by decide

/-- **PATH_MAX counts the NUL.**  4095 content bytes plus the NUL is a
name `getname_flags` accepts: `strncpy_from_user(kname, filename,
PATH_MAX)` returns 4095, below `PATH_MAX`, so the `-ENAMETOOLONG` arm at
`len == PATH_MAX` is not taken (fs/namei.c, `getname_flags`;
include/uapi/linux/limits.h `PATH_MAX` 4096; v6.18.46). -/
theorem pin_read_cstr_4095_fits :
    read_cstr (pin_run 0x1000 4095) 0x1000#64
      = CstrOk (List.replicate 4095 0x61#8) := by
  have h := read_cstr_aux_run 0x1000 4095 (by decide) path_max 0 (Nat.zero_le _)
  rw [Nat.add_zero, Nat.sub_zero] at h
  unfold read_cstr
  rw [h]
  have hlt : 4095 < path_max := by decide
  simp only [hlt, ↓reduceIte]

/-- 4096 content bytes then a NUL: `strncpy_from_user` with count
`PATH_MAX` copies 4096 bytes and returns `PATH_MAX`, and `getname_flags`
answers `-ENAMETOOLONG` (fs/namei.c, `getname_flags`, v6.18.46). -/
theorem pin_read_cstr_4096_too_long :
    read_cstr (pin_run 0x1000 4096) 0x1000#64 = CstrTooLong := by
  have h := read_cstr_aux_run 0x1000 4096 (by decide) path_max 0 (Nat.zero_le _)
  rw [Nat.add_zero, Nat.sub_zero] at h
  unfold read_cstr
  rw [h]
  have hlt : ¬ (4096 < path_max) := by decide
  simp only [hlt, ↓reduceIte]

/-- The 4096-byte name is NOT accepted as a string, and NOT a fault: its
NUL is mapped, one byte past the bound the kernel stops at. -/
theorem pin_read_cstr_4096_not_ok :
    read_cstr (pin_run 0x1000 4096) 0x1000#64
      ≠ CstrOk (List.replicate 4096 0x61#8) := by
  intro hc
  rw [pin_read_cstr_4096_too_long] at hc
  cases hc

theorem pin_read_cstr_4096_not_fault :
    read_cstr (pin_run 0x1000 4096) 0x1000#64 ≠ CstrFault := by
  intro hc
  rw [pin_read_cstr_4096_too_long] at hc
  cases hc

/-- The recorded read set of `"abc\0"` is four bytes: the NUL is read. -/
theorem pin_cstr_access_len_counts_nul :
    cstr_access_len_aux (pin_mem 0x1000 [0x61#8, 0x62#8, 0x63#8, 0#8]) 0x1000#64 path_max
      = 4 := by decide

/-- ...and a fault at the third byte counts three: the faulting byte is an
access the kernel issued. -/
theorem pin_cstr_access_len_counts_faulting_byte :
    cstr_access_len_aux (pin_mem 0x1000 [0x61#8, 0x62#8]) 0x1000#64 path_max = 3 := by
  decide

theorem pin_cstr_access_len_not_content_only :
    cstr_access_len_aux (pin_mem 0x1000 [0x61#8, 0x62#8, 0x63#8, 0#8]) 0x1000#64 path_max
      ≠ 3 := by decide

/-- **copy_from_user is all-or-nothing for `read_bytes_map`.**  A hole in
the middle of the range is `none`: `_inline_copy_from_user` returns the
count of bytes NOT copied (include/linux/uaccess.h,
`_inline_copy_from_user`, v6.18.46), and the callers this walk models
answer `-EFAULT` on any nonzero count. -/
theorem pin_read_bytes_map_hole_is_none :
    read_bytes_map (fun a => if a = 0x1001#64 then none else some 0x61#8)
      0x1000#64 3#64 = none := by decide

theorem pin_read_bytes_map_mapped_is_bytes :
    read_bytes_map (pin_mem 0x1000 [1#8, 2#8, 3#8]) 0x1000#64 3#64
      = some [1#8, 2#8, 3#8] := by decide

/-- A zero-length copy touches no memory: riscv's copier takes the byte
tail for a short count and leaves at once when the cursor is already at
the end, returning 0 (arch/riscv/lib/uaccess.S,
`fallback_scalar_usercopy_sum_enabled`, the `.Lbyte_copy_tail` check and
`.Lout_copy_user`, v6.18.46), whatever the address holds. -/
theorem pin_read_bytes_map_zero_len :
    read_bytes_map (fun _ => none) 0x1000#64 0#64 = some [] := by decide

/-- ...but one byte at that address is a fault. -/
theorem pin_read_bytes_map_one_unmapped_byte :
    read_bytes_map (fun _ => none) 0x1000#64 1#64 = none := by decide

/-- The byte order is the address order: `read_bytes_map` is not reversed
by its accumulator. -/
theorem pin_read_bytes_map_not_reversed :
    read_bytes_map (pin_mem 0x1000 [1#8, 2#8, 3#8]) 0x1000#64 3#64
      ≠ some [3#8, 2#8, 1#8] := by decide

/-- **The readable prefix.**  `"abc"` mapped and 0x1003 not: a
`copy_from_user` of 8 bytes moves the three and faults on the fourth —
`raw_copy_from_user` returns 5 uncopied and the prefix stands
(include/linux/uaccess.h, `_inline_copy_from_user`, v6.18.46).  The count
is byte-exact here because a copy shorter than `9*SZREG-1` bytes takes
the byte-at-a-time tail; in the unrolled word loop a fault inside a batch
of eight loads reports the whole batch uncopied (arch/riscv/lib/uaccess.S,
`fallback_scalar_usercopy_sum_enabled`, v6.18.46), so this pin does not
generalise to a long buffer byte for byte. -/
theorem pin_readable_bytes_prefix :
    readable_bytes (pin_mem 0x1000 [0x61#8, 0x62#8, 0x63#8]) 0x1000#64 8#64
      = [0x61#8, 0x62#8, 0x63#8] := by decide

/-- The prefix stops at the FIRST hole: a mapped byte beyond it is not
reached, so the result is not `"ac"`. -/
theorem pin_readable_bytes_stops_at_first_hole :
    readable_bytes (fun a => if a = 0x1001#64 then none else some 0x61#8)
      0x1000#64 3#64 = [0x61#8] := by decide

theorem pin_readable_bytes_does_not_skip_hole :
    readable_bytes (fun a => if a = 0x1001#64 then none else some 0x61#8)
      0x1000#64 3#64 ≠ [0x61#8, 0x61#8] := by decide

/-- ...and never more than the count asked for. -/
theorem pin_readable_bytes_capped :
    readable_bytes (pin_mem 0x1000 [0x61#8, 0x62#8, 0x63#8]) 0x1000#64 2#64
      = [0x61#8, 0x62#8] := by decide

/-- **read_u64 is little-endian**, as riscv's byte order is
(arch/riscv/include/uapi/asm/byteorder.h includes
linux/byteorder/little_endian.h, v6.18.46): the iovec fields the kernel
copies in are read with byte 0 least significant. -/
theorem pin_read_u64_little_endian :
    read_u64 (pin_mem 0x1000 [1#8, 2#8, 3#8, 4#8, 5#8, 6#8, 7#8, 8#8]) 0x1000#64
      = some 0x0807060504030201#64 := by decide

theorem pin_read_u64_not_big_endian :
    read_u64 (pin_mem 0x1000 [1#8, 2#8, 3#8, 4#8, 5#8, 6#8, 7#8, 8#8]) 0x1000#64
      ≠ some 0x0102030405060708#64 := by decide

/-- Seven mapped bytes are not a word: the eighth faults the read. -/
theorem pin_read_u64_short_is_none :
    read_u64 (pin_mem 0x1000 [1#8, 2#8, 3#8, 4#8, 5#8, 6#8, 7#8]) 0x1000#64 = none := by
  decide

/-- **`__access_ok` at the limit.**  A range ending exactly at `TASK_SIZE`
passes: `addr <= limit - size` with equality (include/asm-generic/
access_ok.h, `__access_ok`, v6.18.46).  One byte further fails. -/
theorem pin_access_okb_ends_at_task_size :
    access_okb (Z_to_bv 64 (TASK_SIZE - 4096)) 4096 = true := by decide

theorem pin_access_okb_past_task_size :
    access_okb (Z_to_bv 64 (TASK_SIZE - 4095)) 4096 = false := by decide

/-- `size <= limit` is tested first: a length over `TASK_SIZE` fails
even at address 0. -/
theorem pin_access_okb_len_over_task_size :
    access_okb 0#64 (TASK_SIZE + 1) = false := by decide

/-- A range wrapping 2^64 is refused: for a size within the limit the
subtraction `limit - size` is what `__access_ok` compares, and
`0xffff_ffff_ffff_fff0` exceeds it; a size over the limit fails the first
conjunct instead. -/
theorem pin_access_okb_wrapping_refused :
    access_okb 0xfffffffffffffff0#64 32 = false := by decide

/-- A zero-length range at `TASK_SIZE` itself passes (`addr <= limit`),
and one byte above it does not (`Checks/Cases/Uaccess.v`'s
`access_ok_at_the_top` and `access_ok_one_past_the_top`). -/
theorem pin_access_okb_zero_at_limit :
    access_okb (Z_to_bv 64 TASK_SIZE) 0 = true := by decide

theorem pin_access_okb_zero_past_limit :
    access_okb (Z_to_bv 64 (TASK_SIZE + 1)) 0 = false := by decide

/-- The case that discriminates the guard from a wrap check: `[2^63,
2^63+8)` does not wrap, and `__access_ok` refuses it on `addr <= limit -
size` alone (include/asm-generic/access_ok.h, `__access_ok`, v6.18.46) —
`Checks/Cases/Uaccess.v`'s `high_range_is_refused`.  The bare walk would
read it on a memory backing that range. -/
theorem pin_access_okb_high_range_refused :
    access_okb (Z_to_bv 64 (2 ^ 63)) 8 = false := by decide

theorem pin_read_bytes_map_high_range_walks :
    read_bytes_map (fun _ => some 0#8) (Z_to_bv 64 (2 ^ 63)) 8#64 ≠ none := by decide

/-- **copy_bytes_map refuses the wrapped range even when the walk would
succeed**: memory answering everywhere, base 16 bytes below the top of
the address space, 32 bytes — `read_bytes_map` wraps and reads, but
`copy_from_user` fails `access_ok` before any copy and returns the whole
count uncopied (include/linux/uaccess.h, `_inline_copy_from_user`,
v6.18.46), on which its callers answer `-EFAULT`. -/
theorem pin_copy_bytes_map_wrapped_refused :
    copy_bytes_map (fun _ => some 0#8) 0xfffffffffffffff0#64 32 = none := by decide

/-- The bare walk DOES read the wrapped range, on purpose: this is what
keeps the refusal above from holding vacuously, the argument
`Checks/Cases/Uaccess.v`'s `wrap_would_pass_a_bare_walk` makes.  Not a
kernel behaviour and not a defect to remove. -/
theorem pin_read_bytes_map_wraps_where_copy_refuses :
    read_bytes_map (fun _ => some 0#8) 0xfffffffffffffff0#64 32#64
      = some (List.replicate 32 0#8) := by decide

/-- ...and an in-range copy is the walk. -/
theorem pin_copy_bytes_map_in_range :
    copy_bytes_map (pin_mem 0x1000 [1#8, 2#8, 3#8]) 0x1000#64 3
      = some [1#8, 2#8, 3#8] := by decide

/-- **`IS_ERR_VALUE`'s band** (include/linux/err.h, `MAX_ERRNO` 4095,
v6.18.46): `-1` and `-4095` are errors; `-4096` and 0 are not, nor is a
user address. -/
theorem pin_addr_is_error_minus_one :
    addr_is_error_b 0xffffffffffffffff#64 = true := by decide

theorem pin_addr_is_error_max_errno :
    addr_is_error_b (Z_to_bv 64 (-4095)) = true := by decide

theorem pin_addr_is_error_below_band :
    addr_is_error_b (Z_to_bv 64 (-4096)) = false := by decide

theorem pin_addr_is_error_zero :
    addr_is_error_b 0#64 = false := by decide

theorem pin_addr_is_error_user_address :
    addr_is_error_b 0x7fff80000000#64 = false := by decide

/-- **`le32_bytes` is the `int` in memory**: the four bytes `do_pipe2`'s
`copy_to_user(fildes, fd, sizeof(fd))` lays down per element (fs/pipe.c,
`do_pipe2`, v6.18.46), least significant first on riscv. -/
theorem pin_le32_bytes_little_endian :
    le32_bytes 0x04030201#64 = [1#8, 2#8, 3#8, 4#8] := by decide

theorem pin_le32_bytes_not_big_endian :
    le32_bytes 0x04030201#64 ≠ [4#8, 3#8, 2#8, 1#8] := by decide

/-- An `int` is four bytes: the upper half of the word is not written. -/
theorem pin_le32_bytes_drops_high_half :
    le32_bytes 0x0100000000#64 = [0#8, 0#8, 0#8, 0#8] := by decide

/-! ## Ticket A12: the signal and terminal state

### `with_killed` / `with_halted`: a death by signal is not an exit

Every claim is about Linux v6.18.46 (commit 1f99e9ab748f).  A fatal
signal with the default disposition ends the process from
`get_signal`, which reaches `do_group_exit(signr)` (kernel/signal.c) with
the SIGNAL NUMBER as the exit code; `exit_group(code)` reaches the same
function with `(error_code & 0xff) << 8` (`SYSCALL_DEFINE1(exit_group)`,
kernel/exit.c).  A waiting parent tells the two apart by `status & 0x7f`
(`wait_task_zombie`, kernel/exit.c, Linux v6.18.46): zero for an exit, the
signal for a
kill.  So `exit(6)`, `exit(134)` and a death by SIGABRT are three
different observations, and the model keeps them apart with one flag. -/

/-- A killed process is OVER, and the payload of the halt is the signal:
`with_killed` writes `procst_halted` (what every "still running?" premise
reads) and sets the flag `m_killed` reads it through. -/
theorem with_killed_ends_the_process_by_the_signal (m : Model) :
    m_halted (with_killed (Z_to_bv 64 6) m) = some (Z_to_bv 64 6)
    ∧ m_killed (with_killed (Z_to_bv 64 6) m) = some (Z_to_bv 64 6) := ⟨rfl, rfl⟩

/-- The refutation: an `exit(6)` is NOT a death by SIGABRT (`status &
0x7f` is 0 for it, `wait_task_zombie`, kernel/exit.c, Linux v6.18.46,
commit 1f99e9ab748f), so `with_halted` with the same payload leaves
`m_killed` `none` — and so does the `exit(134)` a shell would print the
same way. -/
theorem exit_is_not_a_kill (m : Model) :
    m_killed (with_halted (Z_to_bv 64 6) m) = none
    ∧ m_killed (with_halted (Z_to_bv 64 134) m) = none := ⟨rfl, rfl⟩

/-- Nor can a kill be read back as an exit once the flag is set on a
model that was halted by an exit earlier: `with_killed` on top of
`with_halted` is a kill.  (Unreachable in a run — no rule steps out of a
halted configuration — and pinned so that a port that made
`with_killed` carry the old flag instead of writing `true` is caught.) -/
theorem with_killed_overrides_an_earlier_exit (m : Model) :
    m_killed (with_killed (Z_to_bv 64 6) (with_halted (Z_to_bv 64 0) m)) = some (Z_to_bv 64 6) :=
  rfl

/-- The event constructors are distinct: folding `KillEv` into `ExitEv`
would let a program fake its own abort with `exit(6)`. -/
theorem kill_event_is_not_an_exit_event (fs : Fs.Fs) :
    KillEv (Z_to_bv 64 6) fs ≠ ExitEv (Z_to_bv 64 6) fs := fun h => event.noConfusion h

/-- A run starts alive and with no kill recorded, whatever the task
declared: `init_model` clears the flag through `mkModel`.  Stated on the
declaring input as well, because the declaration is the one abort field a
run can start with either value of. -/
theorem init_model_is_not_killed (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_killed (init_model reserved brk0 mbase sp lim inp) = none
    ∧ m_killed (init_model reserved brk0 mbase sp lim
                  { inp with in_abort_terminal := true }) = none := ⟨rfl, rfl⟩

/-! ### `with_sigabrt_pending`: the blocked SIGABRT waits

`__send_signal_locked` adds a signal to `pending->signal` whether or not
it is blocked (kernel/signal.c, Linux v6.18.46, commit 1f99e9ab748f), and
a blocked one stays there until the mask uncovers it; the model records
that one bit, and nothing but the fatal delivery reads it. -/

/-- Sending SIGABRT while it is blocked leaves the process RUNNING: the
pending bit is set and the halt field is untouched. -/
theorem sigabrt_pending_does_not_end_the_process (m : Model) :
    m_sigabrt_pending (with_sigabrt_pending m) = true
    ∧ m_halted (with_sigabrt_pending m) = m_halted m
    ∧ m_killed (with_sigabrt_pending m) = m_killed m := ⟨rfl, rfl, rfl⟩

/-- The refutation: a fresh process has nothing pending — the model's
only sender is the `tkill` arm, and no arm has run — so a port that
seeded the bit from the input's mask would be wrong. -/
theorem init_model_has_no_sigabrt_pending (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_sigabrt_pending (init_model reserved brk0 mbase sp lim inp) = false := rfl

/-! ### `with_sigaltstack_installed`: one bit, cleared by `execve` -/

/-- A starting process has no alternate stack: `begin_new_exec` sets
`me->sas_ss_sp = me->sas_ss_size = 0` (fs/exec.c, Linux v6.18.46, commit
1f99e9ab748f), so `init_model` starts the bit `false` whatever the
launching environment had installed. -/
theorem init_model_has_no_sigaltstack (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_sigaltstack_installed (init_model reserved brk0 mbase sp lim inp) = false := rfl

/-- Once installed, MONOTONE: no setter clears the bit, because the one
call that could shrink `sas_ss_size` back to zero — a later SS_DISABLE
(`do_sigaltstack`, kernel/signal.c, Linux v6.18.46, commit
1f99e9ab748f) — is declined by the very bit this sets.  Pinned through
the setters an intervening syscall would run. -/
theorem sigaltstack_bit_survives_other_setters (v : word) (m : Model) :
    m_sigaltstack_installed
      (with_halted v (with_sigmask v (with_tid v (with_sigaltstack_installed m)))) = true := rfl

/-! ### `with_abort_terminal`: the task's declaration, seeded once

No kernel line: this field is the task's declaration of what the model
covers, not kernel state (see the Rocq field note). -/

/-- `init_model` copies the declaration in, in both stances… -/
theorem init_model_copies_the_declaration (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_abort_terminal (init_model reserved brk0 mbase sp lim
                        { inp with in_abort_terminal := true }) = true
    ∧ m_abort_terminal (init_model reserved brk0 mbase sp lim
                          { inp with in_abort_terminal := false }) = false := ⟨rfl, rfl⟩

/-- …and no other seeding path reaches it: a model built without an
input, through `mkModel`, has the declaration OFF — the stance every
statement in the tree was written under. -/
theorem mkModel_declaration_is_off (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word)
    (tid : Option word) (rlim : Option (List byte)) :
    m_abort_terminal (mkModel fds vm stdin fs halted tid rlim) = false := rfl

/-! ### The stat pins: `statpin_lookup`, `with_statpin`, `statpins_restrict`

The fixture: one file `f` (0x66) holding one byte, and a 4-byte stand-in
for the 128 bytes a real `fstat` delivers. -/

def statpin_fs : Fs.Fs := [([Z_to_bv 8 0x66], [Z_to_bv 8 0x41])]
def statpin_bytes : List byte := [Z_to_bv 8 1, Z_to_bv 8 2, Z_to_bv 8 3, Z_to_bv 8 4]
def statpin_f : Fs.path := [Z_to_bv 8 0x66]
def statpin_g : Fs.path := [Z_to_bv 8 0x67]

/-- A pinned path is found with the bytes it was pinned with… -/
theorem statpin_lookup_finds_the_pin :
    statpin_lookup [(statpin_f, statpin_bytes)] statpin_f = some statpin_bytes := by
  decide +kernel

/-- …and a path never statted has no pin: that is the branch that
CREATES one, so a lookup that answered for an unpinned path would pin
nothing. -/
theorem statpin_lookup_misses_an_unpinned_path :
    statpin_lookup [(statpin_f, statpin_bytes)] statpin_g = none := by
  decide +kernel

/-- `with_statpin` records exactly the delivered bytes under the path. -/
theorem with_statpin_records_the_bytes (m : Model) :
    statpin_lookup (m_statpins (with_statpin statpin_f statpin_bytes m)) statpin_f
      = some statpin_bytes := by
  show statpin_lookup ((statpin_f, statpin_bytes) :: m_statpins m) statpin_f = some statpin_bytes
  rw [statpin_lookup, Fs.path_eqb_refl]
  rfl

/-- A create over an existing file keeps its pin: O_TRUNC resizes the
SAME inode rather than replacing it — `handle_truncate` (fs/namei.c)
calls `do_truncate` (fs/open.c), which sets `ATTR_SIZE` on the opened
dentry through `notify_change`, Linux v6.18.46, commit 1f99e9ab748f —
and `st_size` is not a member the pin holds fixed, so `with_fs` with an
image that still holds the path is inert on the pin (Rocq: the argument
on `State.statpins_restrict`).  The image installed is the TRUNCATED one,
the path now empty, so what is tested is survival across a CHANGED file:
the trace is `create f; write; fstat; open(f, O_TRUNC); fstat`.  Stated
over the unchanged `statpin_fs`, as it first was, the pin was inert: a
`statpins_restrict` that dropped a pin whenever the path's content
changed would have passed it, and would route that trace's second
`fstat` to the pin-creating branch of `fstat_file_spec`
(Sys/Fs/Stat.lean), which admits any well-formed answer — a second
`st_ino` for the one inode `do_open` (fs/namei.c, Linux v6.18.46)
truncates in place, which Linux never returns.  What the EMPTY image adds over
`pin_survives_a_rewrite` (Checks/Cases/Fs/Stat.lean), which grows the
file, is the `some []` lookup: a filter reading an empty file as absent
passes every non-empty image and fails here. -/
theorem with_fs_keeps_a_pin_whose_file_survives :
    m_statpins (with_fs [(statpin_f, [])]
      (with_statpin statpin_f statpin_bytes (mkModel [] (mkVmMaps [] [] 0 0 0) IEof statpin_fs none none none)))
      = [(statpin_f, statpin_bytes)] := by decide +kernel

/-- The refutation: `unlinkat` destroys the inode a pin records
(`vfs_unlink`, fs/namei.c, Linux v6.18.46, commit 1f99e9ab748f), and a
file created at that name afterwards is a NEW inode, so the pin must go
with the file — `with_fs` with an image that no longer holds the path
drops it.  A port that kept it would reject the conforming trace
`create f; fstat; unlink f; create f; fstat`. -/
theorem with_fs_drops_the_pin_of_an_unlinked_file :
    m_statpins (with_fs []
      (with_statpin statpin_f statpin_bytes (mkModel [] (mkVmMaps [] [] 0 0 0) IEof statpin_fs none none none)))
      = [] := by decide +kernel

/-- Only the file's OWN pin goes: an unrelated pin survives the unlink. -/
theorem with_fs_keeps_the_other_files_pins :
    m_statpins (with_fs statpin_fs
      (with_statpin statpin_g statpin_bytes
        (with_statpin statpin_f statpin_bytes (mkModel [] (mkVmMaps [] [] 0 0 0) IEof statpin_fs none none none))))
      = [(statpin_f, statpin_bytes)] := by decide +kernel


/-! ## The iovec family (ticket A4) -/

/-- One LP64 `struct iovec` as user memory holds it: eight little-endian
bytes of `iov_base`, then eight of `iov_len` (include/uapi/linux/uio.h,
`struct iovec`; riscv is little-endian, arch/riscv/include/uapi/asm/byteorder.h;
both v6.18.46). -/
def iov_bytes (base len : word) : List byte := word_le8 base ++ word_le8 len

/-- An iovec array of `iovs` laid out from `lo`, nothing else mapped. -/
def pin_iovs (lo : Nat) (iovs : List (word × word)) : word → Option byte :=
  pin_mem lo (iovs.flatMap fun bl => iov_bytes bl.1 bl.2)

/-! ### `MAX_RW_COUNT` and the scalar clamp

`vfs_read` and `vfs_write` clamp `count` to `MAX_RW_COUNT` after
`rw_verify_area` and before the `->read`/`->write` dispatch
(fs/read_write.c, `vfs_read`, `vfs_write`, v6.18.46): an over-clamp
count is a SHORT transfer, never an errno. -/

/-- The value: `INT_MAX & PAGE_MASK` (include/linux/fs.h, `MAX_RW_COUNT`,
v6.18.46) at the 4 KiB page size, `0x7fffffff & ~0xfff`.
model: the kernel macro is spelled with `INT_MAX` and `PAGE_MASK`, which the evidence checker cannot evaluate; the reading and its 4 KiB-page scope are on `State.MAX_RW_COUNT` and in bugs/max-rw-count-hardcoded-page-size.md. -/
theorem pin_max_rw_count_is_int_max_page_masked :
    MAX_RW_COUNT = (((0x7fffffff : Nat) &&& 0xfffff000 : Nat) : Int) := by decide

/-- ...and not `INT_MAX` itself: a port that dropped the page mask would
name a transfer 4095 bytes longer than any Linux performs.
model: the negation of the value pin above; the kernel reading is on `State.MAX_RW_COUNT`. -/
theorem pin_max_rw_count_is_not_int_max : MAX_RW_COUNT ≠ 0x7fffffff := by decide

/-- ...nor the 16 KiB-page value: the constant is the 4 KiB one on purpose,
the scope bugs/max-rw-count-hardcoded-page-size.md records.
model: the scope choice, argued on `State.MAX_RW_COUNT`; no 16 KiB-page kernel is a supported implementation here. -/
theorem pin_max_rw_count_is_the_4k_value : MAX_RW_COUNT ≠ 0x7fffc000 := by decide

/-- **The scalar clamp is a short transfer, not an error.**  A count one
above `MAX_RW_COUNT` is cut to it by `if (count > MAX_RW_COUNT) count =
MAX_RW_COUNT;` (fs/read_write.c, `vfs_read`, `vfs_write`, v6.18.46).
kernel: fs/read_write.c:vfs_read,vfs_write@v6.18.46 -/
theorem pin_rw_count_clamp_cuts_to_the_cap :
    rw_count_clamp (Z_to_bv 64 (MAX_RW_COUNT + 1)) = MAX_RW_COUNT := by decide

/-- ...and it is not the count asked for: a kernel reporting all of
`MAX_RW_COUNT + 1` moved in one call would be lying.
kernel: fs/read_write.c:vfs_read,vfs_write@v6.18.46 -/
theorem pin_rw_count_clamp_not_the_whole_count :
    rw_count_clamp (Z_to_bv 64 (MAX_RW_COUNT + 1)) ≠ MAX_RW_COUNT + 1 := by decide

/-- Exactly `MAX_RW_COUNT` is untouched, as is any smaller count.  (The
kernel's test is `count > MAX_RW_COUNT`; a min clamp answers the same at
the cap under `>=`, so no pin can separate the two, and none claims to.)
kernel: fs/read_write.c:vfs_read,vfs_write@v6.18.46 -/
theorem pin_rw_count_clamp_at_the_cap_untouched :
    rw_count_clamp (Z_to_bv 64 MAX_RW_COUNT) = MAX_RW_COUNT := by decide

/-- A count under the cap is the transfer size itself.
kernel: fs/read_write.c:vfs_read,vfs_write@v6.18.46 -/
theorem pin_rw_count_clamp_small_untouched : rw_count_clamp 4096#64 = 4096 := by decide

/-- A count the kernel's clamp really sees: 2^32 bytes from a low buffer
passes `vfs_read`'s `access_ok` (2^32 is under `TASK_SIZE`) and is cut to
`MAX_RW_COUNT` at the clamp (fs/read_write.c, `vfs_read`, `vfs_write`,
v6.18.46).
kernel: fs/read_write.c:vfs_read,vfs_write@v6.18.46 -/
theorem pin_rw_count_clamp_four_gib_cuts_to_the_cap :
    rw_count_clamp (Z_to_bv 64 (2 ^ 32)) = MAX_RW_COUNT := by decide

/-- The largest `size_t` clamps too: the helper is total.  The kernel never
reaches its clamp with that count — `vfs_read`'s `access_ok(buf, count)`
refuses any size above `TASK_SIZE` first (fs/read_write.c, `vfs_read`,
v6.18.46) — so this is a statement about the helper, not about a call.
model: `vfs_read` answers -EFAULT at `access_ok` before the clamp for a count above `TASK_SIZE`; the helper's totality is the model's own, and the arm reading it applies `access_ok` first. -/
theorem pin_rw_count_clamp_max_word :
    rw_count_clamp 0xffffffffffffffff#64 = MAX_RW_COUNT := by decide

/-! ### `IOV_MAX`: the count gate, and where it sits

`__import_iovec` takes the single-descriptor path first, then
`iovec_from_user` returns early on a zero count and refuses a count over
`UIO_MAXIOV` before `copy_iovec_from_user` reads anything
(lib/iov_iter.c, `__import_iovec`, `iovec_from_user`, v6.18.46). -/

/-- The value: the model's name for the kernel's `UIO_MAXIOV`
(include/uapi/linux/uio.h, v6.18.46), the bound `iovec_from_user` tests
(lib/iov_iter.c, `iovec_from_user`, v6.18.46).
kernel: include/uapi/linux/uio.h:UIO_MAXIOV; lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem pin_iov_max_is_1024 : IOV_MAX = 1024 := by decide

/-- **A count over `UIO_MAXIOV` is -EINVAL before any descriptor is read.**
`iovec_from_user` tests `nr_segs > UIO_MAXIOV` ahead of its copy
(lib/iov_iter.c, `iovec_from_user`, v6.18.46): with nothing mapped at
all, 1025 descriptors are refused as -EINVAL.  Ticket A4's acceptance
case.
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_1025_is_einval :
    import_iovecs (fun _ => none) 0x1000#64 1025#64 = ImpInval := by decide

/-- ...and NOT -EFAULT, though the array is unreadable: the count test
fires first, so a kernel answering -EFAULT here would have read a
descriptor it never reads.
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_1025_not_efault :
    import_iovecs (fun _ => none) 0x1000#64 1025#64 ≠ ImpFault := by decide

/-- Nothing is recorded as read for a refused count.
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_accesses_1025_empty :
    import_iovecs_accesses (fun _ => none) 0x1000#64 1025#64 = [] := by decide

/-- **Exactly `UIO_MAXIOV` descriptors pass the count test**: the same
unreadable array at count 1024 reaches `copy_iovec_from_user` and faults
on its first descriptor (`UIO_MAXIOV` is 1024, include/uapi/linux/uio.h,
v6.18.46).
kernel: include/uapi/linux/uio.h:UIO_MAXIOV; lib/iov_iter.c:iovec_from_user,copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_1024_reaches_the_copy :
    import_iovecs (fun _ => none) 0x1000#64 1024#64 = ImpFault := by decide

/-- ...and is not refused as -EINVAL: 1024 is not over `UIO_MAXIOV`.
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_1024_not_einval :
    import_iovecs (fun _ => none) 0x1000#64 1024#64 ≠ ImpInval := by decide

/-- **Zero descriptors import nothing and touch nothing.**  `iovec_from_user`
returns before any copy when `nr_segs == 0`, and `__import_iovec`'s loop
then runs zero times (lib/iov_iter.c, `iovec_from_user`, `__import_iovec`,
v6.18.46): the array address is never tested, so even the last address
of the space imports the empty vector.
kernel: lib/iov_iter.c:iovec_from_user,__import_iovec@v6.18.46 -/
theorem pin_import_iovecs_zero_count_is_empty :
    import_iovecs (fun _ => none) 0xffffffffffffffff#64 0#64 = ImpOk [] := by decide

/-- ...and is not -EFAULT for the address it never tested.
kernel: lib/iov_iter.c:iovec_from_user,__import_iovec@v6.18.46 -/
theorem pin_import_iovecs_zero_count_not_efault :
    import_iovecs (fun _ => none) 0xffffffffffffffff#64 0#64 ≠ ImpFault := by decide

/-! ### One descriptor caps before it checks; an array checks before it caps -/

/-- One descriptor: base 0x2000, length 2^47.  Uncapped, the range reaches
the top of the Sv48 user space (`TASK_SIZE`) and `access_ok` refuses it;
capped to `MAX_RW_COUNT` it is ordinary user memory. -/
def iov1_huge : word → Option byte := pin_iovs 0x1000 [(0x2000#64, Z_to_bv 64 (2 ^ 47))]

/-- The same descriptor followed by a harmless one. -/
def iov2_huge : word → Option byte :=
  pin_iovs 0x1000 [(0x2000#64, Z_to_bv 64 (2 ^ 47)), (0x2000#64, 8#64)]

/-- **`nr_segs == 1` caps first.**  `__import_iovec`'s first statement hands
a single descriptor to `__import_iovec_ubuf`, whose `import_ubuf` clamps
`len` to `MAX_RW_COUNT` and only then applies `access_ok` to the clamped
length (lib/iov_iter.c, `__import_iovec_ubuf`, `import_ubuf`, v6.18.46):
the 2^47-byte descriptor imports, uncapped as the entry, because its first
0x7ffff000 bytes are user space.
kernel: lib/iov_iter.c:__import_iovec,__import_iovec_ubuf,import_ubuf@v6.18.46 -/
theorem pin_import_iovecs_single_caps_before_access_ok :
    import_iovecs iov1_huge 0x1000#64 1#64 = ImpOk [(0x2000#64, Z_to_bv 64 (2 ^ 47))] := by
  decide

/-- ...so it is not -EFAULT, which is what checking the uncapped length
would answer.
kernel: lib/iov_iter.c:__import_iovec,__import_iovec_ubuf,import_ubuf@v6.18.46 -/
theorem pin_import_iovecs_single_huge_not_efault :
    import_iovecs iov1_huge 0x1000#64 1#64 ≠ ImpFault := by decide

/-- **Two or more descriptors check the UNCAPPED length.**  `__import_iovec`'s
per-segment loop applies `access_ok(iov_base, len)` before it clamps
(lib/iov_iter.c, `__import_iovec`, v6.18.46), so the same 2^47-byte
descriptor is -EFAULT inside a two-entry array.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem pin_import_iovecs_array_checks_uncapped_length :
    import_iovecs iov2_huge 0x1000#64 2#64 = ImpFault := by decide

/-- ...so the array is not imported: a kernel returning both entries would
have skipped the `access_ok` its loop applies to each.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem pin_import_iovecs_array_huge_not_imported :
    import_iovecs iov2_huge 0x1000#64 2#64
      ≠ ImpOk [(0x2000#64, Z_to_bv 64 (2 ^ 47)), (0x2000#64, 8#64)] := by decide

/-! ### Errno order: the copy pass, then the `access_ok` pass -/

/-- Descriptor 0 names a base `access_ok` refuses (2^63); descriptor 1 has a
length negative as `ssize_t` (2^63). -/
def iov_bad_addr_then_neg : word → Option byte :=
  pin_iovs 0x1000 [(Z_to_bv 64 (2 ^ 63), 8#64), (0x2000#64, Z_to_bv 64 (2 ^ 63))]

/-- **-EINVAL at any index beats `access_ok`'s -EFAULT at any index.**  The
array is copied whole by `copy_iovec_from_user`, which returns -EINVAL
on the negative length at index 1, before `__import_iovec`'s `access_ok`
loop would have reached the bad base at index 0 (lib/iov_iter.c,
`copy_iovec_from_user`, `__import_iovec`, v6.18.46).
kernel: lib/iov_iter.c:copy_iovec_from_user,__import_iovec@v6.18.46 -/
theorem pin_import_iovecs_einval_beats_access_ok_efault :
    import_iovecs iov_bad_addr_then_neg 0x1000#64 2#64 = ImpInval := by decide

/-- ...and not -EFAULT for the bad base at index 0, which the second pass
never reaches.
kernel: lib/iov_iter.c:copy_iovec_from_user,__import_iovec@v6.18.46 -/
theorem pin_import_iovecs_einval_beats_access_ok_efault_not_efault :
    import_iovecs iov_bad_addr_then_neg 0x1000#64 2#64 ≠ ImpFault := by decide

/-- One mapped descriptor with a negative length; at count 2 the second
descriptor's sixteen bytes are unmapped. -/
def iov_neg_then_unmapped : word → Option byte :=
  pin_iovs 0x1000 [(0x2000#64, Z_to_bv 64 (2 ^ 63))]

/-- **Within the copy pass the first error in index order decides.**
`copy_iovec_from_user` is one interleaved walk — each descriptor's two
fields, then its sign test — so a negative length at index 0 answers
-EINVAL though index 1 is unreadable (lib/iov_iter.c,
`copy_iovec_from_user`, v6.18.46).  This is the order of v6.4 and later
(commit 487c20b016dc, named on `State.copy_iovecs_aux`); stable kernels
v4.17 to v6.3 bulk-copied the array first and answered -EFAULT on this
very shape, so the pin states a premise the supported set does not share:
bugs/import-iovecs-copy-order-is-v6.4.md.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_copy_order_negative_first_is_einval :
    import_iovecs iov_neg_then_unmapped 0x1000#64 2#64 = ImpInval := by decide

/-- ...and not -EFAULT for the unreadable descriptor at index 1, which is
never loaded.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_copy_order_negative_first_not_efault :
    import_iovecs iov_neg_then_unmapped 0x1000#64 2#64 ≠ ImpFault := by decide

/-- The mirror image — index 0 unreadable, index 1 negative — is -EFAULT:
the first descriptor faults before the second is loaded.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_copy_order_fault_first_is_efault :
    import_iovecs (pin_mem 0x1010 (iov_bytes 0x2000#64 (Z_to_bv 64 (2 ^ 63)))) 0x1000#64 2#64
      = ImpFault := by decide

/-- ...and not -EINVAL for the negative length at index 1, which is never
loaded.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_copy_order_fault_first_not_einval :
    import_iovecs (pin_mem 0x1010 (iov_bytes 0x2000#64 (Z_to_bv 64 (2 ^ 63)))) 0x1000#64 2#64
      ≠ ImpInval := by decide

/-- Only the `iov_len` half of one descriptor is mapped, holding 2^63; the
`iov_base` half at 0x1000 is not. -/
def iov_len_only : word → Option byte := pin_mem 0x1008 (word_le8 (Z_to_bv 64 (2 ^ 63)))

/-- **Both fields are loaded before the sign is tested.**  `copy_iovec_from_user`
reads `iov_len` and then `iov_base`, each `unsafe_get_user` jumping to
`uaccess_end` with -EFAULT on a fault, and tests `len < 0` only after both
(lib/iov_iter.c, `copy_iovec_from_user`, v6.18.46): a readable negative
length beside an unreadable base is -EFAULT.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_read_iovec_entry_unreadable_base_faults :
    read_iovec_entry iov_len_only 0x1000#64 = IovFault := by decide

/-- ...not -EINVAL, which is what testing the sign between the two loads
would answer (the revision `State.iov_entry` records).
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_read_iovec_entry_unreadable_base_not_einval :
    read_iovec_entry iov_len_only 0x1000#64 ≠ IovInval := by decide

/-- A length with bit 63 set is negative as `ssize_t` and -EINVAL
(`if (unlikely(len < 0)) { ret = -EINVAL; …}`, lib/iov_iter.c,
`copy_iovec_from_user`, v6.18.46)...
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_read_iovec_entry_negative_length_is_einval :
    read_iovec_entry (pin_mem 0x1000 (iov_bytes 0x2000#64 (Z_to_bv 64 (2 ^ 63)))) 0x1000#64
      = IovInval := by decide

/-- ...and one below it is the largest valid descriptor.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_read_iovec_entry_max_positive_length_is_an_entry :
    read_iovec_entry (pin_mem 0x1000 (iov_bytes 0x2000#64 (Z_to_bv 64 (2 ^ 63 - 1)))) 0x1000#64
      = IovEntry 0x2000#64 (Z_to_bv 64 (2 ^ 63 - 1)) := by decide

/-! ### The array is range-checked whole, and each entry is, length 0 included -/

/-- **`user_access_begin` covers the whole array**: `copy_iovec_from_user`
opens with `user_access_begin(uiov, nr_segs * sizeof(*uiov))`
(lib/iov_iter.c, `copy_iovec_from_user`, v6.18.46), so two descriptors
starting sixteen bytes below `TASK_SIZE` (0x800000000000 on Sv48) — the
second straddling the limit — are -EFAULT before either is read, whatever
memory holds there.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_array_past_task_size_is_efault :
    import_iovecs (fun _ => some 0#8) (Z_to_bv 64 (0x800000000000 - 16)) 2#64 = ImpFault := by
  decide

/-- ...while one descriptor there fits exactly and is read: the zeroed
memory decodes to base 0, length 0, which imports.
kernel: lib/iov_iter.c:copy_iovec_from_user,__import_iovec_ubuf@v6.18.46 -/
theorem pin_import_iovecs_array_ending_at_task_size_is_read :
    import_iovecs (fun _ => some 0#8) (Z_to_bv 64 (0x800000000000 - 16)) 1#64
      = ImpOk [(0#64, 0#64)] := by decide

/-- A readable array whose second entry is zero-length at a base `access_ok`
refuses. -/
def iov_zero_len_high : word → Option byte :=
  pin_iovs 0x1000 [(0x2000#64, 8#64), (Z_to_bv 64 (2 ^ 63), 0#64)]

/-- **`access_ok` runs on a zero-length entry too.**  `__import_iovec`'s loop
tests every segment's base, length 0 included (lib/iov_iter.c,
`__import_iovec`, v6.18.46), and `__access_ok(2^63, 0)` fails its
`addr <= limit - size` half (include/asm-generic/access_ok.h,
`__access_ok`, v6.18.46): the import is -EFAULT though no byte of that
entry could move.
kernel: lib/iov_iter.c:__import_iovec; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pin_iovs_access_okb_zero_length_high_refused :
    iovs_access_okb [(0x2000#64, 8#64), (Z_to_bv 64 (2 ^ 63), 0#64)] = false := by decide

/-- The same, end to end: the two-entry array whose zero-length second
entry sits at 2^63 is -EFAULT from the `access_ok` pass.
kernel: lib/iov_iter.c:__import_iovec; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pin_import_iovecs_zero_length_high_is_efault :
    import_iovecs iov_zero_len_high 0x1000#64 2#64 = ImpFault := by decide

/-- ...and is not imported: a port that skipped `access_ok` on zero-length
entries would return both.
kernel: lib/iov_iter.c:__import_iovec; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pin_import_iovecs_zero_length_high_not_imported :
    import_iovecs iov_zero_len_high 0x1000#64 2#64
      ≠ ImpOk [(0x2000#64, 8#64), (Z_to_bv 64 (2 ^ 63), 0#64)] := by decide

/-- ...and a zero-length entry in user space passes, like any other.
kernel: lib/iov_iter.c:__import_iovec; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pin_iovs_access_okb_zero_length_low_accepted :
    iovs_access_okb [(0x2000#64, 8#64), (0x3000#64, 0#64)] = true := by decide

/-! ### The descriptor ledger -/

/-- **The faulting descriptor is a recorded access.**  With descriptor 0
readable and descriptor 1 not, `copy_iovec_from_user` reached two
descriptors, sixteen bytes each, before -EFAULT (lib/iov_iter.c,
`copy_iovec_from_user`, v6.18.46); the ledger holds both and no third.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_copy_iovecs_accesses_records_the_faulting_descriptor :
    copy_iovecs_accesses (pin_iovs 0x1000 [(0x2000#64, 3#64)]) 0x1000#64 3
      = [(0x1000#64, 16), (0x1010#64, 16)] := by decide

/-- ...and the third descriptor, behind the fault, is not recorded.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_copy_iovecs_accesses_stops_at_the_fault :
    copy_iovecs_accesses (pin_iovs 0x1000 [(0x2000#64, 3#64)]) 0x1000#64 3
      ≠ [(0x1000#64, 16), (0x1010#64, 16), (0x1020#64, 16)] := by decide

/-- The single-descriptor path reads exactly one descriptor.
kernel: lib/iov_iter.c:__import_iovec_ubuf,copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_accesses_single :
    import_iovecs_accesses iov1_huge 0x1000#64 1#64 = [(0x1000#64, 16)] := by decide

/-! ### The layout decode (`read_iovecs`, the conformance tester's reader) -/

/-- **The LP64 layout**: `iov_base` at offset 0 and `iov_len` at offset 8
— `struct iovec`'s order, a pointer then a `__kernel_size_t`
(include/uapi/linux/uio.h, v6.18.46) — the fields `copy_iovec_from_user`
loads through `&uiov->iov_len` and `&uiov->iov_base` (lib/iov_iter.c,
`copy_iovec_from_user`, v6.18.46), each eight little-endian bytes.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_read_iovecs_two_entries :
    read_iovecs (pin_iovs 0x1000 [(0x2000#64, 3#64), (0x3000#64, 5#64)]) 0x1000#64 2#64
      = some [(0x2000#64, 3#64), (0x3000#64, 5#64)] := by decide

/-- ...and not with the fields swapped: a decoder taking `iov_len` first
answers the pairs reversed.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_read_iovecs_not_swapped :
    read_iovecs (pin_iovs 0x1000 [(0x2000#64, 3#64), (0x3000#64, 5#64)]) 0x1000#64 2#64
      ≠ some [(3#64, 0x2000#64), (5#64, 0x3000#64)] := by decide

/-- A descriptor with an unmapped byte fails the whole decode, as the
kernel's copy faults: `none`, not a shorter list.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_read_iovecs_short_array_is_none :
    read_iovecs (pin_iovs 0x1000 [(0x2000#64, 3#64), (0x3000#64, 5#64)]) 0x1000#64 3#64
      = none := by decide

/-! ### The aggregate clamp (`cap_iovecs`) -/

/-- **The clamp truncates in place and keeps the tail.**  `__import_iovec`'s
loop cuts the entry that crosses `MAX_RW_COUNT` to the remaining budget
and every later entry to 0, leaving `nr_segs` unchanged (lib/iov_iter.c,
`__import_iovec`, v6.18.46): the second entry becomes 16 bytes, the
third 0 (Rocq: `Checks/Cases/Prelude.v`'s
`cap_iovecs_truncates_in_place_and_keeps_the_tail`, over the same
`cap_boundary_iovecs`).
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem pin_cap_iovecs_truncates_in_place_and_keeps_the_tail :
    cap_iovecs cap_boundary_iovecs
      = [(4096#64, Z_to_bv 64 (MAX_RW_COUNT - 16)), (8192#64, 16#64), (12288#64, 0#64)] := by
  decide

/-- ...and the aggregate is exactly `MAX_RW_COUNT`.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem pin_cap_iovecs_total_is_the_cap :
    iovs_total (cap_iovecs cap_boundary_iovecs) = MAX_RW_COUNT := by decide

/-- The tail entry is not dropped: an import that shortened `nr_segs` would
address-check two entries where the kernel checks three.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem pin_cap_iovecs_keeps_nr_segs :
    cap_iovecs cap_boundary_iovecs
      ≠ [(4096#64, Z_to_bv 64 (MAX_RW_COUNT - 16)), (8192#64, 16#64)] := by
  decide

/-- Under the cap nothing changes.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem pin_cap_iovecs_under_the_cap_untouched :
    cap_iovecs [(4096#64, 100#64), (8192#64, 50#64)] = [(4096#64, 100#64), (8192#64, 50#64)] := by
  decide

/-! ### Scatter and gather

`iterate_iovec` walks the segments in order, takes `min(len, iov_len)`
from each, skips a segment whose part is 0 without calling the step, and
breaks out after a short step (include/linux/iov_iter.h, `iterate_iovec`,
v6.18.46); the steps are `copy_to_user_iter` and `copy_from_user_iter`
(lib/iov_iter.c, v6.18.46), whose raw copies return the uncopied count.
Every vector below has two entries or more: one descriptor imports as an
`ITER_UBUF`, which `iterate_ubuf` walks in a single step with the same
result (include/linux/iov_iter.h, `iterate_ubuf`, `iterate_and_advance2`,
v6.18.46). -/

/-- **A delivery is split across the destinations in order**, each piece
written whole.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_scatter_iovecs_splits_in_order :
    scatter_iovecs (pin_mem 0x2000 (List.replicate 5 0#8)) [(0x2000#64, 2#64), (0x2002#64, 3#64)]
        [1#8, 2#8, 3#8, 4#8, 5#8]
      = some [(0x2000#64, [1#8, 2#8]), (0x2002#64, [3#8, 4#8, 5#8])] := by decide

/-- **A zero-length destination produces no write at all**: `iterate_iovec`
skips a segment whose `part` is 0 without calling the step (`if
(likely(part))`, include/linux/iov_iter.h, `iterate_iovec`, v6.18.46),
so its base is never touched — here it is not even mapped.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_scatter_iovecs_skips_zero_length :
    scatter_iovecs (pin_mem 0x2000 (List.replicate 2 0#8)) [(0x7000#64, 0#64), (0x2000#64, 2#64)]
        [1#8, 2#8]
      = some [(0x2000#64, [1#8, 2#8])] := by decide

/-- ...and not a vacuous empty write to it.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_scatter_iovecs_no_vacuous_write :
    scatter_iovecs (pin_mem 0x2000 (List.replicate 2 0#8)) [(0x7000#64, 0#64), (0x2000#64, 2#64)]
        [1#8, 2#8]
      ≠ some [(0x7000#64, []), (0x2000#64, [1#8, 2#8])] := by decide

/-- More bytes than the vector holds is refused.  This `none` is the only
bound the readv channel and connected-socket arms put on a delivery's
length: they choose the bytes with no bound of their own and keep those
the scatter places, as the kernel's copy is cut to the iterator's count
(`len = iter->count`, include/linux/iov_iter.h:296-297, v6.18.46).
kernel: include/linux/iov_iter.h:iterate_and_advance2@v6.18.46 -/
theorem pin_scatter_iovecs_over_capacity_is_none :
    scatter_iovecs (pin_mem 0x2000 (List.replicate 5 0#8)) [(0x2000#64, 2#64)] [1#8, 2#8, 3#8]
      = none := by decide

/-- A destination byte that is not writable refuses the scatter; which
errno or short count the consuming arm makes of that is the arm's
decision, not this walk's.
model: a closed answer of the model's own guard; the arm reading it decides the kernel outcome. -/
theorem pin_scatter_iovecs_unwritable_is_none :
    scatter_iovecs (pin_mem 0x2000 [0#8]) [(0x2000#64, 2#64)] [1#8, 2#8] = none := by decide

/-- Sources `"ab"` at 0x2000 and `"c"` at 0x3000. -/
def src_ab_c : word → Option byte := fun a =>
  if a = 0x2000#64 then some 0x61#8
  else if a = 0x2001#64 then some 0x62#8
  else if a = 0x3000#64 then some 0x63#8
  else none

/-- The same with 0x2001 unmapped. -/
def src_a_hole_c : word → Option byte := fun a =>
  if a = 0x2001#64 then none else src_ab_c a

/-- **The gathered string is the sources in vector order** — the buffer one
`write` of the concatenation would move.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_gather_iovecs_in_order :
    gather_iovecs src_ab_c [(0x2000#64, 2#64), (0x3000#64, 1#64)]
      = some [0x61#8, 0x62#8, 0x63#8] := by decide

/-- A hole anywhere makes the whole gather `none`: the all-readable
condition `gather_prefix` weakens.
model: a closed answer of the model's own all-or-nothing gather; the kernel's short-copy behaviour is pinned on `gather_prefix` below. -/
theorem pin_gather_iovecs_hole_is_none :
    gather_iovecs src_a_hole_c [(0x2000#64, 2#64), (0x3000#64, 1#64)] = none := by decide

/-- **A fault inside a source stops the gather there.**  `iterate_iovec`
breaks out of its loop when a step copies short (`if (skip < p->iov_len)
break;`, include/linux/iov_iter.h, `iterate_iovec`, v6.18.46), so the
bytes before the hole are moved and the next source is never read:
`"a"`, not `"ac"`.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_gather_prefix_stops_at_the_fault :
    gather_prefix src_a_hole_c [(0x2000#64, 2#64), (0x3000#64, 1#64)] = [0x61#8] := by decide

/-- ...and it is not `"ac"`: a gather that stepped over the hole to the
next source would move a byte the kernel never reads.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_gather_prefix_does_not_skip_the_fault :
    gather_prefix src_a_hole_c [(0x2000#64, 2#64), (0x3000#64, 1#64)] ≠ [0x61#8, 0x63#8] := by
  decide

/-- With every source readable the prefix is the whole flattening.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_gather_prefix_complete_when_readable :
    gather_prefix src_ab_c [(0x2000#64, 2#64), (0x3000#64, 1#64)] = [0x61#8, 0x62#8, 0x63#8] := by
  decide

/-- A zero-length source is skipped without its base being read (0x7000 is
unmapped), and the gather continues past it.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_gather_prefix_skips_zero_length_source :
    gather_prefix src_ab_c [(0x2000#64, 2#64), (0x7000#64, 0#64), (0x3000#64, 1#64)]
      = [0x61#8, 0x62#8, 0x63#8] := by decide

/-- `writev_gathered` is the prefix over the CAPPED vector; under the cap it
is the flattening.  The over-cap half — that the gather stops at
`MAX_RW_COUNT` — is not a `decide` pin (it needs that many readable source
bytes); the cap it composes is pinned on `cap_iovecs` above, the
composition is Rocq's one-line definition, and the arm that consumes it
(`writev`) pins the clamp end to end when it is ported.
kernel: lib/iov_iter.c:__import_iovec; include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_writev_gathered_under_the_cap :
    writev_gathered src_ab_c [(0x2000#64, 2#64), (0x3000#64, 1#64)] = [0x61#8, 0x62#8, 0x63#8] := by
  decide

/-! ### The copy-in ledger of a short transfer -/

/-- A 6-byte delivery into 4 + 4 touched all of the first destination and
two bytes of the second — the `part` of each segment `iterate_iovec`
handed its step (include/linux/iov_iter.h, `iterate_iovec`, v6.18.46).
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_iov_prefix_accesses_short_transfer :
    iov_prefix_accesses [(0x2000#64, 4#64), (0x3000#64, 4#64)] 6
      = [(0x2000#64, 4), (0x3000#64, 2)] := by decide

/-- ...and not the whole second destination: only the delivered part of a
segment was touched.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_iov_prefix_accesses_not_the_whole_vector :
    iov_prefix_accesses [(0x2000#64, 4#64), (0x3000#64, 4#64)] 6
      ≠ [(0x2000#64, 4), (0x3000#64, 4)] := by decide

/-- A zero-length entry contributes no range.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_iov_prefix_accesses_skips_zero_length :
    iov_prefix_accesses [(0x7000#64, 0#64), (0x2000#64, 4#64)] 2 = [(0x2000#64, 2)] := by decide


/-! ### Decisions the pins above left implicit -/

/-- The decoder's fuel stops at `UIO_MAXIOV` whatever the count, and loses
nothing by it: `iovec_from_user` refuses a larger count before any
descriptor is copied (lib/iov_iter.c, `iovec_from_user`, v6.18.46), so
no admitted call imports more.
model: the bound is the conformance tester's fuel, argued on `State.read_iovecs`; the kernel's refusal of the count is `pin_import_iovecs_1025_is_einval`. -/
theorem pin_read_iovecs_fuel_stops_at_iov_max (mp : word → Option byte) (a : word) :
    read_iovecs mp a 1025#64 = read_iovecs_aux mp a 1024 := by
  unfold read_iovecs
  exact congrArg (read_iovecs_aux mp a) (by decide)

/-- **The aggregate is summed without wrapping**: two entries of 2^63 bytes
total 2^64, where a word-summed port would answer 0 and let writev's
-EFAULT gate see nothing requested.
model: a closed computation over `iovs_total`, which sums in `Int` by construction (`State.iovs_total`); no kernel outcome is claimed. -/
theorem pin_iovs_total_does_not_wrap :
    iovs_total [(0#64, Z_to_bv 64 (2 ^ 63)), (0#64, Z_to_bv 64 (2 ^ 63))] = 2 ^ 64 := by decide

/-- The mirror of the unreadable base: only the `iov_base` half is mapped
(holding 0x2000) and the `iov_len` half at 0x1008 is not.  `iov_len` is
the FIRST field `copy_iovec_from_user` loads, and it faults
(lib/iov_iter.c, `copy_iovec_from_user`, v6.18.46).
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_read_iovec_entry_unreadable_length_faults :
    read_iovec_entry (pin_mem 0x1000 (word_le8 0x2000#64)) 0x1000#64 = IovFault := by decide

/-- The ledger of a two-entry import is the copy pass's, even when the
`access_ok` pass then fails: both descriptors were loaded before
`__import_iovec` refused the first segment's range (lib/iov_iter.c,
`copy_iovec_from_user`, `__import_iovec`, v6.18.46).
kernel: lib/iov_iter.c:copy_iovec_from_user,__import_iovec@v6.18.46 -/
theorem pin_import_iovecs_accesses_array_is_the_copy_pass :
    import_iovecs_accesses iov2_huge 0x1000#64 2#64 = [(0x1000#64, 16), (0x1010#64, 16)] := by
  decide

/-- ...and an array `user_access_begin` refuses records nothing: no
descriptor was loaded.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_accesses_array_past_task_size_empty :
    import_iovecs_accesses (fun _ => some 0#8) (Z_to_bv 64 (0x800000000000 - 16)) 2#64 = [] := by
  decide

/-- A one-byte delivery into a destination as long as the cap touches one
byte — `iterate_iovec` hands its step `min(len, iov_len)` = 1
(include/linux/iov_iter.h, `iterate_iovec`, v6.18.46) — and the ledger
computes it without materializing the 0x7ffff000-byte length, which is
why `iov_prefix_accesses` bounds with `word_to_nat_bounded`.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_iov_prefix_accesses_capped_length_one_byte :
    iov_prefix_accesses [(0x2000#64, 0x7ffff000#64)] 1 = [(0x2000#64, 1)] := by decide


/-! ### Added in review: the shapes the section above left unpinned -/

/-! ### The single-descriptor path's errno arms, and its two `access_ok` tests failing

`__import_iovec_ubuf` returns `copy_iovec_from_user(iov, uvec, 1)`'s errno
unchanged (`if (unlikely(ret)) return ret;`) and then `import_ubuf`'s
(lib/iov_iter.c, `__import_iovec_ubuf`, v6.18.46): the same -EFAULT and
-EINVAL as the array path, decided by the same loads, and the descriptor
array itself is range-checked by `user_access_begin(uiov, sizeof(*uiov))`
exactly as a longer array is. -/

/-- **One negative length is -EINVAL through the single path too.**
`copy_iovec_from_user` with `nr_segs = 1` tests `len < 0` after its two
loads and `__import_iovec_ubuf` hands the -EINVAL straight back
(lib/iov_iter.c, `copy_iovec_from_user`, `__import_iovec_ubuf`, v6.18.46).
kernel: lib/iov_iter.c:__import_iovec_ubuf,copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_single_negative_length_is_einval :
    import_iovecs (pin_mem 0x1000 (iov_bytes 0x2000#64 (Z_to_bv 64 (2 ^ 63)))) 0x1000#64 1#64
      = ImpInval := by decide

/-- ...and not -EFAULT: a port with the two constructors crossed on the
single path would report the sign test as a fault.
kernel: lib/iov_iter.c:__import_iovec_ubuf,copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_single_negative_length_not_efault :
    import_iovecs (pin_mem 0x1000 (iov_bytes 0x2000#64 (Z_to_bv 64 (2 ^ 63)))) 0x1000#64 1#64
      ≠ ImpFault := by decide

/-- **One unreadable descriptor is -EFAULT through the single path**: the
first `unsafe_get_user` faults and `__import_iovec_ubuf` returns it
(lib/iov_iter.c, `copy_iovec_from_user`, `__import_iovec_ubuf`, v6.18.46).
kernel: lib/iov_iter.c:__import_iovec_ubuf,copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_single_unreadable_is_efault :
    import_iovecs (fun _ => none) 0x1000#64 1#64 = ImpFault := by decide

/-- ...and not -EINVAL: nothing was read, so no length was tested.
kernel: lib/iov_iter.c:__import_iovec_ubuf,copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_single_unreadable_not_einval :
    import_iovecs (fun _ => none) 0x1000#64 1#64 ≠ ImpInval := by decide

/-- **The one-descriptor array is range-checked too**: `copy_iovec_from_user`
opens with `user_access_begin(uiov, 1 * sizeof(*uiov))`, `access_ok` on
riscv (arch/riscv/include/asm/uaccess.h, `user_access_begin`, v6.18.46),
so an array whose sixteen bytes straddle `TASK_SIZE` is -EFAULT before
its one descriptor is read, whatever memory holds there.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_single_array_past_task_size_is_efault :
    import_iovecs (fun _ => some 0#8) (Z_to_bv 64 (0x800000000000 - 8)) 1#64 = ImpFault := by
  decide

/-- ...and the zeroed memory there is not decoded into the entry {0, 0} a
port that skipped the array check would import.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_single_array_past_task_size_not_imported :
    import_iovecs (fun _ => some 0#8) (Z_to_bv 64 (0x800000000000 - 8)) 1#64
      ≠ ImpOk [(0#64, 0#64)] := by decide

/-- Nothing is recorded as read for the refused one-descriptor array.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_accesses_single_array_past_task_size_empty :
    import_iovecs_accesses (fun _ => some 0#8) (Z_to_bv 64 (0x800000000000 - 8)) 1#64 = [] := by
  decide

/-- **The capped `access_ok` still refuses a base outside user space**: a
zero-length lone descriptor at 2^63 is `import_ubuf`'s `access_ok(2^63, 0)`,
which fails its `addr <= limit - size` half (lib/iov_iter.c, `import_ubuf`;
include/asm-generic/access_ok.h, `__access_ok`; v6.18.46) — the shape
`testing/syscall-check/tests/writev_import.c`'s `zero-hi` case probes.
kernel: lib/iov_iter.c:import_ubuf; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pin_import_iovecs_single_zero_length_high_is_efault :
    import_iovecs (pin_iovs 0x1000 [(Z_to_bv 64 (2 ^ 63), 0#64)]) 0x1000#64 1#64 = ImpFault := by
  decide

/-- ...and is not imported: a port that dropped the single path's `access_ok`
because the cap had already been applied would return the entry.
kernel: lib/iov_iter.c:import_ubuf; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pin_import_iovecs_single_zero_length_high_not_imported :
    import_iovecs (pin_iovs 0x1000 [(Z_to_bv 64 (2 ^ 63), 0#64)]) 0x1000#64 1#64
      ≠ ImpOk [(Z_to_bv 64 (2 ^ 63), 0#64)] := by decide

/-- The cap does not rescue a base too close to the limit: 2^47 bytes from
`TASK_SIZE - 0x1000` cap to `MAX_RW_COUNT`, and `access_ok` of that range
still ends past `TASK_SIZE` (lib/iov_iter.c, `import_ubuf`, v6.18.46).
kernel: lib/iov_iter.c:import_ubuf; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pin_import_iovecs_single_capped_range_still_past_limit :
    import_iovecs (pin_iovs 0x1000 [(Z_to_bv 64 (0x800000000000 - 0x1000), Z_to_bv 64 (2 ^ 47))])
        0x1000#64 1#64 = ImpFault := by decide

/-! ### The boundary Rocq's `Checks/Cases/Fs/ReadWrite.v` probes: capped range ending exactly at `TASK_SIZE` -/

/-- Rocq's `readv_cap_order_base`/`readv_cap_order_len` fixture (`Checks/Cases/Fs/ReadWrite.v`,
`readv_single_iovec_caps_before_access_ok`): a descriptor whose CAPPED range
ends exactly at `TASK_SIZE` (the Sv48 top, 0x800000000000, spelled as a
numeral in the pins below because no cited function spells `TASK_SIZE`)
and whose uncapped range ends one byte past it, followed by {NULL, 0}. -/
def iov_cap_order : word → Option byte :=
  pin_iovs 0x2000
    [(Z_to_bv 64 (TASK_SIZE - MAX_RW_COUNT), Z_to_bv 64 (MAX_RW_COUNT + 1)), (0#64, 0#64)]

/-- **At count 1 the capped range fits exactly and imports**: `import_ubuf`
clamps the length to `MAX_RW_COUNT` and `__access_ok` accepts
`addr <= limit - size` at equality (lib/iov_iter.c, `import_ubuf`;
include/asm-generic/access_ok.h, `__access_ok`; v6.18.46).  A port with `<`
for the kernel's `<=` would refuse it (Rocq: `readv_single_iovec_caps_before_access_ok`).
kernel: lib/iov_iter.c:import_ubuf; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pin_import_iovecs_cap_order_single_imports :
    import_iovecs iov_cap_order 0x2000#64 1#64
      = ImpOk [(Z_to_bv 64 (0x800000000000 - MAX_RW_COUNT), Z_to_bv 64 (MAX_RW_COUNT + 1))] := by
  decide

/-- ...while at count 2 the UNCAPPED range ends one byte past `TASK_SIZE`
and `__import_iovec`'s loop refuses it (lib/iov_iter.c, `__import_iovec`,
v6.18.46).
kernel: lib/iov_iter.c:__import_iovec; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pin_import_iovecs_cap_order_array_faults :
    import_iovecs iov_cap_order 0x2000#64 2#64 = ImpFault := by decide

/-- ...and the two answers differ by the count alone: the same memory, the
same first descriptor.
kernel: lib/iov_iter.c:__import_iovec_ubuf,__import_iovec@v6.18.46 -/
theorem pin_import_iovecs_cap_order_array_not_imported :
    import_iovecs iov_cap_order 0x2000#64 2#64
      ≠ ImpOk [(Z_to_bv 64 (0x800000000000 - MAX_RW_COUNT), Z_to_bv 64 (MAX_RW_COUNT + 1)),
               (0#64, 0#64)] := by decide

/-! ### The success shape: two descriptors, in index order -/

/-- A readable two-descriptor array: {0x2000, 3} then {0x3000, 5}. -/
def iov_two : word → Option byte := pin_iovs 0x1000 [(0x2000#64, 3#64), (0x3000#64, 5#64)]

/-- **Two descriptors import in index order.**  `copy_iovec_from_user`
stores each `iov[i]` as it walks `uiov++`, and `__import_iovec`'s
`access_ok` loop passes both (lib/iov_iter.c, `copy_iovec_from_user`,
`__import_iovec`, v6.18.46): the shape every real two-iovec `readv` and
`writev` takes.
kernel: lib/iov_iter.c:copy_iovec_from_user,__import_iovec@v6.18.46 -/
theorem pin_import_iovecs_two_entries_in_order :
    import_iovecs iov_two 0x1000#64 2#64 = ImpOk [(0x2000#64, 3#64), (0x3000#64, 5#64)] := by
  decide

/-- ...and not reversed: a port consing the tail first would scatter into
0x3000 before 0x2000.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_two_entries_not_reversed :
    import_iovecs iov_two 0x1000#64 2#64 ≠ ImpOk [(0x3000#64, 5#64), (0x2000#64, 3#64)] := by
  decide

/-- ...nor emptied by the `access_ok` pass: both entries survive it.
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem pin_import_iovecs_two_entries_not_dropped :
    import_iovecs iov_two 0x1000#64 2#64 ≠ ImpOk [] := by decide

/-- The ledger of a successful two-descriptor import is both descriptors
(`testing/syscall-check/tests/readv_spec.c` rebuilds exactly this ledger).
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_accesses_two_entries :
    import_iovecs_accesses iov_two 0x1000#64 2#64 = [(0x1000#64, 16), (0x1010#64, 16)] := by
  decide

/-- ...and no third: the walk is `nr_segs` descriptors long.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_accesses_two_entries_no_third :
    import_iovecs_accesses iov_two 0x1000#64 2#64
      ≠ [(0x1000#64, 16), (0x1010#64, 16), (0x1020#64, 16)] := by decide

/-! ### The ledger after a negative length; the length half alone unreadable

`pin_read_iovec_entry_unreadable_length_faults` above is the positive half
of the length-half case; its refutation and the end-to-end shape follow. -/

/-- **A negative length is recorded and stops the walk**: `copy_iovec_from_user`
loads both halves of the descriptor, then `goto uaccess_end` with -EINVAL,
so the descriptor was attempted and no later one is (lib/iov_iter.c,
`copy_iovec_from_user`, v6.18.46) — `testing/syscall-check/tests/writev_import.c`'s
`neglen` case rejects a ledger that reaches descriptor 2.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_copy_iovecs_accesses_records_the_negative_descriptor_and_stops :
    copy_iovecs_accesses iov_neg_then_unmapped 0x1000#64 3 = [(0x1000#64, 16)] := by decide

/-- ...and does not walk past it to the next descriptor.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_copy_iovecs_accesses_does_not_pass_a_negative_length :
    copy_iovecs_accesses iov_neg_then_unmapped 0x1000#64 3
      ≠ [(0x1000#64, 16), (0x1010#64, 16)] := by decide

/-- ...and is not defaulted to a zero-length entry at the readable base.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_read_iovec_entry_unreadable_length_not_an_entry :
    read_iovec_entry (pin_mem 0x1000 (word_le8 0x2000#64)) 0x1000#64 ≠ IovEntry 0x2000#64 0#64 := by
  decide

/-- Rocq's `mem_readv_len_only` shape end to end (`Checks/Cases/Fs/ReadWrite.v`,
`readv_unreadable_base_faults_before_the_sign_test`): the first descriptor's
base bytes absent, its length 2^63, a second descriptor readable — the
import faults on descriptor 0 and the ledger is that one descriptor.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_accesses_len_only_first_descriptor :
    import_iovecs_accesses
        (pin_mem 0x1008 (word_le8 (Z_to_bv 64 (2 ^ 63)) ++ word_le8 4096#64 ++ word_le8 1#64))
        0x1000#64 2#64
      = [(0x1000#64, 16)] := by decide

/-- ...and that import is -EFAULT, not the -EINVAL a sign test between the
loads would give.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_len_only_first_descriptor_is_efault :
    import_iovecs
        (pin_mem 0x1008 (word_le8 (Z_to_bv 64 (2 ^ 63)) ++ word_le8 4096#64 ++ word_le8 1#64))
        0x1000#64 2#64
      = ImpFault := by decide

/-! ### A fault at a segment's first byte is a stop, not a zero-length skip -/

/-- **An unreadable first byte stops the gather; it is not a zero-length
skip.**  With `part > 0` the step copies nothing, `skip` stays 0 and
`skip < p->iov_len` breaks the loop (include/linux/iov_iter.h,
`iterate_iovec`, v6.18.46): the two bytes before the unreadable segment
move, and the readable segment behind it is never read.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_gather_prefix_unreadable_first_byte_stops :
    gather_prefix src_ab_c [(0x2000#64, 2#64), (0x7000#64, 1#64), (0x3000#64, 1#64)]
      = [0x61#8, 0x62#8] := by decide

/-- ...and the segment is not skipped like a zero-length one: a port testing
"nothing readable" where the kernel tests "the whole segment copied" would
deliver `"c"` from a source the kernel never reaches.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_gather_prefix_unreadable_segment_not_skipped :
    gather_prefix src_ab_c [(0x2000#64, 2#64), (0x7000#64, 1#64), (0x3000#64, 1#64)]
      ≠ [0x61#8, 0x62#8, 0x63#8] := by decide

/-- A hole at the very first byte gathers nothing at all.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem pin_gather_prefix_first_segment_unreadable_is_empty :
    gather_prefix src_ab_c [(0x7000#64, 1#64), (0x3000#64, 1#64)] = [] := by decide

/-! ### Scatter checks the delivered part, not the whole destination -/

/-- **Only the delivered part must be writable.**  `iterate_iovec` hands
`copy_to_user_iter` `part = min(len, iov_len)` bytes and nothing past them
(include/linux/iov_iter.h, `iterate_iovec`; lib/iov_iter.c,
`copy_to_user_iter`, whose `access_ok` and raw copy cover `len` bytes;
v6.18.46): a two-byte delivery into a four-byte destination of which only
the first two bytes are mapped succeeds.
kernel: include/linux/iov_iter.h:iterate_iovec; lib/iov_iter.c:copy_to_user_iter@v6.18.46 -/
theorem pin_scatter_iovecs_checks_the_delivered_part_only :
    scatter_iovecs (pin_mem 0x2000 (List.replicate 2 0#8)) [(0x2000#64, 4#64)] [1#8, 2#8]
      = some [(0x2000#64, [1#8, 2#8])] := by decide

/-- ...and is not refused for the two unmapped bytes the delivery never
reaches: a port checking the whole `iov_len` would fault a short read that
Linux completes.
kernel: include/linux/iov_iter.h:iterate_iovec; lib/iov_iter.c:copy_to_user_iter@v6.18.46 -/
theorem pin_scatter_iovecs_unmapped_tail_beyond_the_part_is_not_a_fault :
    scatter_iovecs (pin_mem 0x2000 (List.replicate 2 0#8)) [(0x2000#64, 4#64)] [1#8, 2#8]
      ≠ none := by decide

/-! ### The count gate beats the array's own `access_ok` -/

/-- **A count over `UIO_MAXIOV` is -EINVAL whatever the array's address**:
`iovec_from_user` tests `nr_segs > UIO_MAXIOV` before it calls
`copy_iovec_from_user`, whose `user_access_begin` is the first look at
the array (lib/iov_iter.c, `iovec_from_user`, `copy_iovec_from_user`,
v6.18.46), so 1025 descriptors at an array straddling `TASK_SIZE` are
-EINVAL, not the -EFAULT the array would earn at any smaller count.
kernel: lib/iov_iter.c:iovec_from_user,copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_count_gate_beats_array_access_ok :
    import_iovecs (fun _ => none) (Z_to_bv 64 (0x800000000000 - 8)) 1025#64 = ImpInval := by
  decide

/-- ...and not -EFAULT: a port range-checking the array before it counts
would answer for an address the kernel never tests here.
kernel: lib/iov_iter.c:iovec_from_user,copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_count_gate_beats_array_access_ok_not_efault :
    import_iovecs (fun _ => none) (Z_to_bv 64 (0x800000000000 - 8)) 1025#64 ≠ ImpFault := by
  decide

/-! ### The ledger at exactly `UIO_MAXIOV` -/

/-- **The ledger passes the count gate where the import does**: at exactly
1024 descriptors `iovec_from_user` does not refuse, `copy_iovec_from_user`
attempts the first descriptor and faults on it (lib/iov_iter.c,
`iovec_from_user`, `copy_iovec_from_user`, v6.18.46), so the ledger is that
one descriptor.
kernel: lib/iov_iter.c:iovec_from_user,copy_iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_accesses_1024_records_the_first_descriptor :
    import_iovecs_accesses (fun _ => none) 0x1000#64 1024#64 = [(0x1000#64, 16)] := by decide

/-- ...and is not empty, which is what a ledger refusing 1024 as over the
limit — the count test at `≥` instead of `>` — would record.
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_accesses_1024_not_refused :
    import_iovecs_accesses (fun _ => none) 0x1000#64 1024#64 ≠ [] := by decide

/-! ### The empty cases, and the aggregate at exactly the cap -/

/-- A zero count decodes the empty array without reading (the fuel bound
itself is `pin_read_iovecs_fuel_stops_at_iov_max` above).
model: the conformance tester's reader; the kernel's zero-count answer is pinned on `import_iovecs`. -/
theorem pin_read_iovecs_zero_count_is_empty :
    read_iovecs (fun _ => none) 0x1000#64 0#64 = some [] := by decide

/-- A vector whose first entry is exactly `MAX_RW_COUNT` leaves nothing for
the second: `len > MAX_RW_COUNT - total_len` with `total_len` already at
the cap cuts it to 0 (lib/iov_iter.c, `__import_iovec`, v6.18.46).
kernel: lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem pin_cap_iovecs_exactly_at_the_cap_zeroes_the_rest :
    cap_iovecs [(4096#64, Z_to_bv 64 MAX_RW_COUNT), (8192#64, 1#64)]
      = [(4096#64, Z_to_bv 64 MAX_RW_COUNT), (8192#64, 0#64)] := by decide

/-- The ledger of a zero count is empty: nothing was read.
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem pin_import_iovecs_accesses_zero_count_empty :
    import_iovecs_accesses (fun _ => none) 0xffffffffffffffff#64 0#64 = [] := by decide

/-- A transfer of nothing touches nothing, and an empty vector has nothing to
touch (`iterate_iovec` is not entered for `len = 0`: `iterate_and_advance2`
returns first, include/linux/iov_iter.h, v6.18.46).
kernel: include/linux/iov_iter.h:iterate_and_advance2,iterate_iovec@v6.18.46 -/
theorem pin_iov_prefix_accesses_nothing_delivered :
    iov_prefix_accesses [(0x2000#64, 4#64)] 0 = [] ∧ iov_prefix_accesses [] 6 = [] := by decide

/-! ## A17: FdFileRW and FdFileA -/

/-- Rocq: `State.pipe_end_live`, State.v:4354 at 96c2debdb.  A read-write
file is not a pipe end, so the scan passes over it to the write end
behind it: only a pipe's own descriptors move `pipe->writers`
(`pipe_release`, fs/pipe.c, Linux v6.18.46).
kernel: fs/pipe.c:pipe_release@v6.18.46 -/
theorem a17_pipe_end_live_skips_rdwr :
    pipe_end_live [(3, .FdFileRW [102] 0), (4, .FdPipe 7 true)] 7 true = true := by
  rfl

/-- Rocq: `State.pipe_end_live`, State.v:4354 at 96c2debdb.  A read-write
file alone keeps no pipe end live: it holds no reference `pipe_release`
(fs/pipe.c, Linux v6.18.46) would drop from `pipe->writers`.
kernel: fs/pipe.c:pipe_release@v6.18.46 -/
theorem a17_rdwr_is_not_a_pipe_end :
    pipe_end_live [(3, .FdFileRW [102] 0)] 7 true = false := by
  rfl

/-- Rocq: `State.pipe_end_live`, State.v:4353 at 96c2debdb.  An
append-mode file is not a pipe end, so the scan passes over it to the
write end behind it: only a pipe's own descriptors move `pipe->writers`
(`pipe_release`, fs/pipe.c, Linux v6.18.46).
kernel: fs/pipe.c:pipe_release@v6.18.46 -/
theorem a17_pipe_end_live_skips_append :
    pipe_end_live [(3, .FdFileA [102] 0), (4, .FdPipe 7 true)] 7 true = true := by
  rfl

/-- Rocq: `State.pipe_end_live`, State.v:4353 at 96c2debdb.  An
append-mode file alone keeps no pipe end live: it holds no reference
`pipe_release` (fs/pipe.c, Linux v6.18.46) would drop from
`pipe->writers`.
kernel: fs/pipe.c:pipe_release@v6.18.46 -/
theorem a17_append_is_not_a_pipe_end :
    pipe_end_live [(3, .FdFileA [102] 0)] 7 true = false := by
  rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.State
