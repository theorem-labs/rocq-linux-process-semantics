import LinuxProcessSemantics.LinuxProcessSem.State
import LinuxProcessSemantics.LinuxProcessSem.MemImageType
import LinuxProcessSemantics.LinuxProcessSem.StackLayout
import LinuxProcessSemantics.LinuxProcessSem.SysSimp
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.TacticCore

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570
unported: rlim_model -- the same model as `demo_model`, which every fixture builds on; prlimit64 pins say `demo_model`
unported: uts_name_of -- defined in `Checks/Cases/Kernel/Sys.lean`, beside the uname pins whose Rocq twins use it
unported: uts_demo -- built by `uts_name_of`, in `Checks/Cases/Kernel/Sys.lean`
unported: uts_demo_b -- built by `uts_name_of`, in `Checks/Cases/Kernel/Sys.lean`
unported: uts_bad_sysname -- built from `uts_literal`, in `Checks/Cases/Kernel/Sys.lean`
unported: uts_unterminated_release -- built from `uts_literal`, in `Checks/Cases/Kernel/Sys.lean`
unported: uts_model -- the same model as `demo_model`; uname pins say `demo_model`
unported: uts_pinned -- `with_utsname uts_demo demo_model`, in `Checks/Cases/Kernel/Sys.lean` -/

/-! # Checks.Cases.PreludeCore — fixtures the check files share

Mirrors the definitions of `theories/LinuxProcessSem/Checks/Cases/Prelude.v`.
Not part of the trusted specification.  This file holds what the per-syscall
check files build on: the demo constants, the process every check starts
from, one builder whose slots are the subsystems a fixture varies, the
user-memory maps a call's arguments point at, and the `rfl` lemmas that read
each of those back.  The rule for the Rocq file's `Example`s and `Lemma`s:
every one of them other than `demo_top_is_alloc_top` pins something that is
not a fixture — `StackLayout`, `Run`, `Sys.Syscall`, the checker — and is
owed to the subject it pins, not to this file; this register does not
track them, so a twin of one is found under its subject or not at all.

The header block above has the shape `tools/check_lean_spec_parity.py`
reads, but that tool scopes itself to the `Sys/` twins and the base files
and does not read this one; until it does, the register is compared against
the Rocq file by hand, and the baseline names a commit whose Rocq file that
comparison covered — move it whenever the Rocq file is re-read.  It was
left at f44244ad through two Rocq changes (#712 and #827) before the second
review of PR #736 noticed `demo_input_tmp` missing, and the repoint of every
twin's baseline at a71fd38a, the squash of that work, moved this one without
the comparison a move stands for: a header nothing reads is kept honest only
by the reviewer who reads it.

HOW A FIXTURE IS SHAPED.  Every model a check runs on is `fixture_of` at
eight slots — the fd table, the pipe buffers, the VM ledger, standard input,
the accept queue, the file system, the core-limit record and the UTS name —
built directly
from `Model`'s constructor, with every other field at the value
`State.init_model` gives the demo input (`demo_model_eq_fixture_of` is the
check that it does).  A slot is LIVE: every argument the builder is handed
lands in a field of the result.  (`fixture` as PR #718 wrote it handed
`h.vm_limit` to `init_model` for `with_vmmaps` to discard a moment later —
the dead-parameter finding this file answers.)  A post-state the spec
produces and the `fixture_of` a check writes down meet under `sys_norm` as
one constructor tree — the next paragraph says why it is a tree and not the
folded spelling — and the fold lemmas below state the same meeting on the
folded spelling, for a hand proof.  The eight are the six subsystems a
fixture varies plus the two records a Rocq fixture pins by setter, the core
limit (`rlim_pinned`) and the UTS name (`uts_pinned`); a pin that needs
another field adds a slot here rather than stacking a setter.  Until
one does, every other setter has no slot and stays applied on top, as
Rocq's fixtures apply them (`Fs/Stat.lean` stacks `with_statpin` so).

HOW A FIXTURE ENTERS `sys_simp`.  `Checks/Cases/Tactic.lean` reads a spec
with one simp set and says a fixture joins it in one of two ways, never
both: opaque with its projection and fold lemmas at the default priority,
or unfolded by its own equation at `low`.  The two symbolic builders
here, `fixture_of` and `fixture`, take the second way (the probe fixture
below is the deliberate counterexample), and the reason is where a spec's
model comes from.  `sys_norm`
simplifies the continuation of `get_model` UNDER its binder before the
reading substitutes the model into it, so by the time a fixture arrives
every getter and setter in the continuation has already been unfolded on a
symbolic `m`, and what the fixture lands in is a raw projection
`(fixture_of …).m_fd` that no `m_*` or `with_*` lemma matches
(`projection_registration_leaves_raw_projections` below states that
residue, and `projection_registration_dies_under_get_model` that the
folded statement is then not closed: the negative half of this
paragraph).  The one spec that reads its ledger DIRECTLY, `munmap_spec`
through `get_vmmaps`, is the other case: the reading hands the fixture to
the continuation whole and the setter meets it only afterwards, so there
a projection lemma and a fold both match and the folded statement closes
(`projection_registration_reads_under_get_vmmaps` below, against
`bare_fixture_dies_under_get_vmmaps` on a fixture registered neither
way).  No check runs a symbolic fixture on `munmap_spec`; the rule above
is the rule for every check there is, and the pair below is what a
second direct reader would be measured against.  The normal form of a model under
`sys_norm` is therefore its constructor tree, and a fixture meets it only
by becoming one.  A CLOSED model — `demo_model`, `one_map_model`, every
literal ledger below, and any model a check file defines from them — needs
no line in the register at all: `sys_norm`'s second pass evaluates every
closed term, so such a model is a tree by the time the two sides are
compared, registered or not.  One shape still wants a line, in the check
file that owns the model.  Where a spec MATCHES on a getter of the model,
the first pass leaves the raw projection on the opaque NAME,
`statat_exists_model.m_fsys.fsst_image`, as the match's discriminant: the
getter was unfolded on the symbolic `m` before the name was substituted,
and the name has no unfolding in the set.  The second pass does open it —
the name becomes its tree — but ground evaluation can stall inside the
lookup it uncovers (`Fs.fs_lookup`'s `ite`, unfolded before its `path_eqb`
condition is decided), and no reading fires on a stuck match.  Registering
the projection's value at the default priority, the first way, puts the
literal list under the match in the FIRST pass, where the closed lookup
facts registered beside it fire: `Fs/Stat.lean`'s `fs_statat_exists_model`
is the instance.  A getter-form lemma such as `Fs/Sync.lean`'s
`m_fds_fsync_model` is not one: its left side `m_fds fsync_model` never
meets the projection chain the first pass leaves, so under `sys_norm` it is
inert, and it earns its keep only as an explicit rewrite.  What the register
HERE has to supply is the unfolding of a fixture with a SYMBOLIC argument,
which the second pass cannot touch: `fixture_of.eq_1` at `low`, and
`fixture_eq_fixture_of` at `low` so that the `fixture h` a check states its
post-state with reaches it.  Those two lines are the whole register, and
`#check_prelude_register` at the end of the file fails the build the day a
third is added.  The projection and fold lemmas stated on `fixture_of`, `fixture` and
`demo_model` below are readable facts and not members of the set, and have to be: with the
unfolding registered, `simp` rewrites the child `fixture_of …` before it
looks at `m_vmmaps (fixture_of …)`, so a projection lemma on the latter
would never be tried (`symbolic_fixture_unfolding_kills_projection` in
`Tactic.lean`).  They are kept for the reader and for a hand proof.

Ticket D2's acceptance line in the port plan, "every fixture has
projection lemmas in sys_simp" (D2 landed as #736), predates #733's
tactic, which made a projection lemma unreachable for any fixture a spec
meets through `get_model`; the section on `opaque_probe` below carries the
argument, and the plan still carries the line, which is a docs change of
its own. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The demo constants -/

/-- The shape `elf-snapshot` emits for a static riscv64 binary whose phdr
table sits at file offset 64 in the first LOAD segment (mapped at
0x10000), with 6 ELF64 program headers. -/
def demo_phdrs : PhdrInfo := PhdrInfo.mkPhdrInfo 0x10040 56 6

/-- The allocation budget (`State.vm_limit`) these demo checks run under:
1 GiB — far above every grant they make, so the budget gate is live but never
the deciding conjunct except where a check says so explicitly. -/
def demo_limit : Int := 0x40000000

/-- The stack pointer these demo checks are started with: the bottom of
the SP window, so their grant top (`State.alloc_top`) is the lowest any
admissible run has and every literal below is admitted by every run.
`demo_top` is that top, spelled once. -/
def demo_sp : word := Z_to_bv 64 sp_window_lo
def demo_top : Int := sp_window_lo - stack_max_size

theorem demo_top_is_alloc_top (reserved : List (word × word)) (brk0 mbase : word)
    (lim : Int) (inp : ProcInput) :
    alloc_top (m_vmmaps (init_model reserved brk0 mbase demo_sp lim inp)) = demo_top := rfl

/-- The launching user is an ORDINARY one, not root, so every check runs
unprivileged.  The group is a DIFFERENT number from the user on purpose: a
state where the two coincide cannot tell a `getgid` wired to `cr_uid` from
one wired to `cr_gid`, and the conformance harness cannot supply the
difference either, since it runs as uid 1000, gid 1000 (the Rocq
`demo_uid` note). -/
def demo_uid : word := Z_to_bv 64 1000
def demo_gid : word := Z_to_bv 64 1002

/-- The AT_HWCAP word the fixtures launch with: the one of `Run.valid_hwcap`'s
two WITHOUT V, so that no check here is a statement about vector dispatch
(the Rocq `demo_hwcap` note; `Checks.PilotEntry` covers the other mask). -/
def demo_hwcap : word := hwcap_rv64gc

/-- A demo AT_RANDOM draw (the `ed_random` half of `Run.ExecEntry`'s
`en_draw`): sixteen bytes,
all different and none zero, so a check that reads byte `k` of the block is
told apart from one that reads byte `j` and from one that still reads the old
zeros.  Any `BitVec 128` is a draw the kernel can make. -/
def demo_random : BitVec 128 := Z_to_bv 128 0x0f1e2d3c4b5a69788796a5b4c3d2e1f0

/-- A demo slack draw (`StackLayout.EntryDraw`'s `ed_slack`): the bytes of
the entry stack's last page above the block.  0x5a at an address one below a
page boundary and 0xa5 elsewhere, so a check can tell "reads the draw AT
THIS address" from "reads a constant".  Nothing constrains this function. -/
def demo_slack : word → byte :=
  fun a => if bv_unsigned a % 4096 = 4095 then Z_to_bv 8 0x5a else Z_to_bv 8 0xa5

/-- The two draws together, and the all-zero draw the model used to behave
as though every kernel made. -/
def demo_draw : EntryDraw := EntryDraw.mkDraw demo_random demo_slack
def zero_draw : EntryDraw := EntryDraw.mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0)

/-- THREE supplementary groups, ascending, and none of them 3.  The number
`getgroups` reports is the LENGTH of this list, so a fixture whose length
coincided with one of its elements — or with a uid, a gid, or the size
argument a check passes — could not tell the model that counts from one that
reports a member.  Ascending because that is the order the kernel stores:
`SYSCALL_DEFINE2(setgroups)` calls `groups_sort` on the list it was handed
before installing it, and `SYSCALL_DEFINE2(getgroups)` copies the stored
order out through `groups_to_user` (kernel/groups.c, Linux v6.18.46, commit
1f99e9ab748f), so this is a list a real `struct group_info` could hold. -/
def demo_groups : List word :=
  [Z_to_bv 64 27, Z_to_bv 64 1002, Z_to_bv 64 4000]

/-- The process input the checks run on: no arguments and no environment,
because nothing they check reads either, which leaves the file system and
the standard-input stream as the only two things a call site states.  The
accept queue is `State.net_silent`: every peer connects, sends nothing and
closes; a check that needs a connection with content names its own queue
(the Rocq `demo_input` note, which also says why the checks that need a
NONEMPTY argv spell `mkProcInput` out instead). -/
def demo_input (fs0 : Fs.Fs) (stdin0 : InputStream) : ProcInput :=
  ProcInput.mkProcInput [] [] fs0 stdin0 demo_uid demo_gid demo_groups net_silent
              default_nofile (Z_to_bv 64 0) demo_hwcap false .Sv48

/-- The same, with a DECLARED PRIVATE /tmp beside the image
(`State.in_tmp`): the entries are keyed by their one component, and
`State.init_model` seeds them under "/tmp/" (`State.fs_seed_tmp`), dropping
a name with a NUL byte in it, which no pathname can spell.  `demo_input` is
this one with the empty declaration, and the empty declaration seeds
nothing, so the file system the run starts with is the image itself.  Rocq
proves the last as `State.fs_seed_tmp_nil`; here each of the three claims
is a `rfl` pin below (`demo_input_tmp_seeds_under_tmp`,
`demo_input_tmp_nul_name_not_seeded`, `demo_input_tmp_nil_in_fs`). -/
def demo_input_tmp (fs0 tmp0 : Fs.Fs) (stdin0 : InputStream) : ProcInput :=
  ProcInput.mkProcInput_full [] [] fs0 stdin0 demo_uid demo_gid demo_groups net_silent
              default_nofile (Z_to_bv 64 0) demo_hwcap false .Sv48 default_urandom tmp0

/-- The credentials `demo_input` produces: an ordinary user whose real,
effective and saved ids all agree, because `State.init_model` derives the
effective and saved ones from the real one it is given (the citation is on
`init_model`). -/
def demo_creds : Creds :=
  Creds.mkCreds demo_uid demo_uid demo_uid demo_gid demo_gid demo_gid demo_groups

/-! ### What the constants have to be, pinned

Each of these is a claim the docstring above it makes about a fixture value;
a fixture that lost the property would silently weaken every check that
relies on it, and nothing else reads the docstrings. -/

theorem bv_unsigned_demo_sp : bv_unsigned demo_sp = sp_window_lo := by decide

/-- The user and the group are different numbers (`demo_uid`'s note). -/
theorem demo_uid_ne_demo_gid : demo_uid ≠ demo_gid := by decide

/-- `demo_input` is `demo_input_tmp` with the empty declaration
(`demo_input_tmp`'s note). -/
theorem demo_input_is_demo_input_tmp_nil (fs0 : Fs.Fs) (stdin0 : InputStream) :
    demo_input fs0 stdin0 = demo_input_tmp fs0 [] stdin0 := rfl

/-- The two `Fs.Fs` arguments land where their names say — the first is
the image, the second the private /tmp.  A same-typed swap of them, which
the constructor call would accept, already fails
`demo_input_is_demo_input_tmp_nil` (the swapped twin's image would be
`[]`); what only this pin refuses is the DEAD-PARAMETER port, `… IEof []`
with `tmp0` never read, on which that theorem is still `rfl` — the shape
PR #718's `fixture` had, which the header recalls. -/
theorem demo_input_tmp_fields (fs0 tmp0 : Fs.Fs) (stdin0 : InputStream) :
    (demo_input_tmp fs0 tmp0 stdin0).in_image_fs = fs0
      ∧ (demo_input_tmp fs0 tmp0 stdin0).in_tmp = tmp0 :=
  ⟨rfl, rfl⟩

/-- The empty declaration seeds nothing: the file system the run starts
with is the image itself (`demo_input_tmp`'s note; Rocq's
`State.fs_seed_tmp_nil`). -/
theorem demo_input_tmp_nil_in_fs (fs0 : Fs.Fs) (stdin0 : InputStream) :
    (demo_input_tmp fs0 [] stdin0).in_fs = fs0 := rfl

/-- A declared entry is seeded under "/tmp/" by `init_model`, keyed by its
one component: "out" lands at `tmp_key [111, 117, 116]`, whatever the image
and the bytes.  Stated through `init_model` rather than `in_fs` because the
claim is about the model a run starts in, and every hand-built /tmp fixture
(`fixture_of (fs := fs_seed_tmp …)`) bypasses `init_model`. -/
theorem demo_input_tmp_seeds_under_tmp (fs0 : Fs.Fs) (bs : List byte) (stdin0 : InputStream) :
    m_fs (init_model [] 0 0 demo_sp demo_limit
            (demo_input_tmp fs0 [([111, 117, 116], bs)] stdin0))
      = Fs.fs_set fs0 (tmp_key [111, 117, 116]) bs := rfl

/-- …and a name with a NUL byte in it is dropped, not seeded: `read_cstr`
stops at the first NUL, so no pathname a program passes names such an entry
(`State.tmp_nul_free`'s note).  The negative of the pin above: the same
declaration with a NUL in its name leaves the image untouched. -/
theorem demo_input_tmp_nul_name_not_seeded (fs0 : Fs.Fs) (bs : List byte) (stdin0 : InputStream) :
    m_fs (init_model [] 0 0 demo_sp demo_limit
            (demo_input_tmp fs0 [([111, 0, 117, 116], bs)] stdin0))
      = fs0 := rfl

/-- Three groups, 3 is none of them, and 3 is neither the uid nor the gid
(`demo_groups`'s note): so a count of 3 is a count. -/
theorem demo_groups_length_is_no_member :
    demo_groups.length = 3 ∧ (Z_to_bv 64 3 ∉ demo_groups)
      ∧ demo_uid ≠ Z_to_bv 64 3 ∧ demo_gid ≠ Z_to_bv 64 3 := by decide

/-- …and ascending, the order `groups_sort` leaves. -/
theorem demo_groups_ascending :
    demo_groups.Pairwise (fun a b => bv_unsigned a < bv_unsigned b) := by decide

/-- The sixteen bytes AT_RANDOM points at under `demo_random` are pairwise
different and none is zero (`demo_random`'s note). -/
theorem demo_random_bytes_distinguishing :
    (at_random_bytes demo_random).length = 16
      ∧ (at_random_bytes demo_random).Nodup
      ∧ Z_to_bv 8 0 ∉ at_random_bytes demo_random := by decide

/-- `demo_slack` answers 0x5a exactly one byte below a page boundary and 0xa5
elsewhere, so it is read AT an address rather than as a constant. -/
theorem demo_slack_marks_the_page_end :
    demo_slack (Z_to_bv 64 4095) = Z_to_bv 8 0x5a ∧ demo_slack (Z_to_bv 64 4096) = Z_to_bv 8 0xa5
      ∧ demo_slack (Z_to_bv 64 8191) = Z_to_bv 8 0x5a ∧ demo_slack (Z_to_bv 64 0) = Z_to_bv 8 0xa5 := by
  decide

/-! ## The base process, and the slots a fixture varies

`demo_model` is Rocq's `init_model [] 0 0 demo_sp demo_limit (demo_input []
IEof)`, the process every Rocq check file starts from under one local name
or another (`rlim_model`, `uts_model`, `statat_absent_model`, `m0`, …); here
it has one name.  `init_fds` and `demo_vm` are the two of its fields that
`init_model` builds rather than copies from its input, spelled exactly as
`init_model` spells them so the projections below are `rfl`. -/

/-- The three standard channels `State.init_model` installs. -/
def init_fds : List (word × FdEntry) :=
  [ (Z_to_bv 64 0, .FdChannel (Z_to_bv 64 0)),
    (Z_to_bv 64 1, .FdChannel (Z_to_bv 64 1)),
    (Z_to_bv 64 2, .FdChannel (Z_to_bv 64 2)) ]

/-- The ledger `State.init_model` builds from the demo arguments: nothing
reserved, nothing live, brk at 0, a 1 GiB budget, no mmap base recorded, and
the stack pointer at `demo_sp`. -/
def demo_vm : VmMaps := VmMaps.mkVmMapsFull [] [] [] 0 0 demo_limit 0 demo_sp

/-- The process every fixture starts from: the demo input, an empty file
system, standard input at end of file, started at `demo_sp` under a 1 GiB
budget. -/
def demo_model : Model := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)

/-- A demo process with eight fields set to the given values: the fd table,
the pipe buffers, the VM ledger, standard input, the accept queue, the file
system, the core-limit record and the UTS name.  Every slot defaults to `demo_model`'s
field, so a check names the slots it varies — `fixture_of (fds := …) (fs :=
…)` — and the result is the same term whichever way it was written.  The
fields with no slot are what the projections below read off. -/
def fixture_of (fds : List (word × FdEntry) := init_fds)
    (pipes : List (word × PipeBuf) := [])
    (h : VmMaps := demo_vm)
    (stdin : InputStream := IEof)
    (net : NetQueue := net_silent)
    (fs : Fs.Fs := [])
    (rlim : Option (List byte) := none)
    (utsname : Option (List byte) := none) : Model :=
  Model.mkModelOf (FdState.mkFdState fds pipes) (VmState.mkVmState h [] [])
    (IoState.mkIoState stdin default_urandom net (Z_to_bv 64 0)) (FsState.mkFsState fs)
    (ProcState.mkProcState none none demo_creds false (Z_to_bv 64 0) false utsname
       false false false false [])
    (LimState.mkLimState rlim default_nofile) (TimeState.mkTimeState (Z_to_bv 64 0))

/-! ### `fixture_of`: projections and setter folds

The projections read a slot back; the folds say what a setter applied to
a fixture is, as the fixture with that slot replaced.  All `rfl`, and none
of them is in `sys_simp` (the header says why): they are the folded
spelling of what `sys_norm` shows as a constructor tree, for a reader or a
hand proof. -/

section fixture_of_lemmas
variable (fds : List (word × FdEntry)) (pipes : List (word × PipeBuf)) (h : VmMaps)
  (stdin : InputStream) (net : NetQueue) (fs : Fs.Fs) (rlim utsname : Option (List byte))

theorem m_fds_fixture_of : m_fds (fixture_of fds pipes h stdin net fs rlim utsname) = fds := rfl
theorem m_pipes_fixture_of : m_pipes (fixture_of fds pipes h stdin net fs rlim utsname) = pipes := rfl
theorem m_vmmaps_fixture_of : m_vmmaps (fixture_of fds pipes h stdin net fs rlim utsname) = h := rfl
theorem m_vm_lazy_fixture_of : m_vm_lazy (fixture_of fds pipes h stdin net fs rlim utsname) = [] := rfl
theorem m_vm_materialized_fixture_of :
    m_vm_materialized (fixture_of fds pipes h stdin net fs rlim utsname) = [] := rfl
theorem m_stdin_fixture_of : m_stdin (fixture_of fds pipes h stdin net fs rlim utsname) = stdin := rfl
theorem m_urandom_fixture_of :
    m_urandom (fixture_of fds pipes h stdin net fs rlim utsname) = default_urandom := rfl
theorem m_net_fixture_of : m_net (fixture_of fds pipes h stdin net fs rlim utsname) = net := rfl
theorem m_conn_ix_fixture_of : m_conn_ix (fixture_of fds pipes h stdin net fs rlim utsname) = Z_to_bv 64 0 := rfl
theorem m_fs_fixture_of : m_fs (fixture_of fds pipes h stdin net fs rlim utsname) = fs := rfl
theorem m_halted_fixture_of : m_halted (fixture_of fds pipes h stdin net fs rlim utsname) = none := rfl
theorem m_tid_fixture_of : m_tid (fixture_of fds pipes h stdin net fs rlim utsname) = none := rfl
theorem m_setsid_succeeded_fixture_of :
    m_setsid_succeeded (fixture_of fds pipes h stdin net fs rlim utsname) = false := rfl
theorem m_has_children_fixture_of :
    m_has_children (fixture_of fds pipes h stdin net fs rlim utsname) = false := rfl
theorem m_sigmask_fixture_of : m_sigmask (fixture_of fds pipes h stdin net fs rlim utsname) = Z_to_bv 64 0 := rfl
theorem m_rlimit_core_fixture_of : m_rlimit_core (fixture_of fds pipes h stdin net fs rlim utsname) = rlim := rfl
theorem m_nofile_fixture_of : m_nofile (fixture_of fds pipes h stdin net fs rlim utsname) = default_nofile := rfl
theorem m_clock_fixture_of : m_clock (fixture_of fds pipes h stdin net fs rlim utsname) = Z_to_bv 64 0 := rfl
theorem m_creds_fixture_of : m_creds (fixture_of fds pipes h stdin net fs rlim utsname) = demo_creds := rfl
theorem m_utsname_fixture_of : m_utsname (fixture_of fds pipes h stdin net fs rlim utsname) = utsname := rfl
theorem m_sigaltstack_installed_fixture_of :
    m_sigaltstack_installed (fixture_of fds pipes h stdin net fs rlim utsname) = false := rfl
theorem m_killed_fixture_of : m_killed (fixture_of fds pipes h stdin net fs rlim utsname) = none := rfl
theorem m_sigabrt_pending_fixture_of :
    m_sigabrt_pending (fixture_of fds pipes h stdin net fs rlim utsname) = false := rfl
theorem m_abort_terminal_fixture_of :
    m_abort_terminal (fixture_of fds pipes h stdin net fs rlim utsname) = false := rfl
theorem m_statpins_fixture_of : m_statpins (fixture_of fds pipes h stdin net fs rlim utsname) = [] := rfl

theorem with_fds_fixture_of (fds' : List (word × FdEntry)) :
    with_fds fds' (fixture_of fds pipes h stdin net fs rlim utsname) = fixture_of fds' pipes h stdin net fs rlim utsname := rfl
theorem with_pipes_fixture_of (pipes' : List (word × PipeBuf)) :
    with_pipes pipes' (fixture_of fds pipes h stdin net fs rlim utsname) = fixture_of fds pipes' h stdin net fs rlim utsname := rfl
theorem with_vmmaps_fixture_of (h' : VmMaps) :
    with_vmmaps h' (fixture_of fds pipes h stdin net fs rlim utsname) = fixture_of fds pipes h' stdin net fs rlim utsname := rfl
theorem with_vm_backing_nil_fixture_of :
    with_vm_backing [] [] (fixture_of fds pipes h stdin net fs rlim utsname) = fixture_of fds pipes h stdin net fs rlim utsname := rfl
theorem with_stdin_fixture_of (stdin' : InputStream) :
    with_stdin stdin' (fixture_of fds pipes h stdin net fs rlim utsname) = fixture_of fds pipes h stdin' net fs rlim utsname := rfl
theorem with_net_fixture_of (net' : NetQueue) :
    with_net net' (fixture_of fds pipes h stdin net fs rlim utsname) = fixture_of fds pipes h stdin net' fs rlim utsname := rfl
theorem with_fs_fixture_of (fs' : Fs.Fs) :
    with_fs fs' (fixture_of fds pipes h stdin net fs rlim utsname) = fixture_of fds pipes h stdin net fs' rlim utsname := rfl
theorem with_rlimit_core_fixture_of (bs : List byte) :
    with_rlimit_core bs (fixture_of fds pipes h stdin net fs rlim utsname)
      = fixture_of fds pipes h stdin net fs (some bs) utsname := rfl
theorem with_utsname_fixture_of (bs : List byte) :
    with_utsname bs (fixture_of fds pipes h stdin net fs rlim utsname)
      = fixture_of fds pipes h stdin net fs rlim (some bs) := rfl

end fixture_of_lemmas

-- `low` for uniformity with every other unfolding in the register, not
-- because anything here needs it: priority orders the candidates at ONE
-- node, and nothing else in the set rewrites a `fixture_of` application, so
-- the word decides nothing (measured: the tree builds unchanged at the
-- default priority).  Nor is it what would let a projection lemma on
-- `m_vmmaps (fixture_of …)` fire: that lemma sits at the parent node, and
-- the child is unfolded first at any priority
-- (`symbolic_fixture_unfolding_kills_projection` in `Tactic.lean`).
attribute [sys_simp low] fixture_of.eq_1

/-! ### Why the register unfolds `fixture_of` rather than projecting it

`opaque_probe` is `fixture_of` at its VM slot under another name (the
`example` below pins that), registered the OTHER way: by a projection and
a fold at the default priority and nothing else.  `get_model_probe` is the
smallest spec that reaches a fixture the way every real spec does, through
`get_model`.  The argument is a differential over ONE statement, the call
against the FOLDED fixture: `projection_registration_dies_under_get_model`
pins that `sys_norm` does not close it on `opaque_probe`
(`fail_if_success`), and `unfolding_registration_closes_under_get_model`
that the same tactic closes it on `fixture_of (h := h)`, whose only
registration is the `fixture_of.eq_1` line above — the register's first
line; `fixture_reaches_its_unfolding_under_get_model`, beside the second
line, does the same for the `fixture h` a check spells its post-state
with.  Neither half is vacuous: the same tactic on the same shape answers
differently, and the registration is the only difference.

Read the contrast as unfolding against everything else, not as unfolding
against projecting.  `opaque_probe`'s two lemmas are inert in its own pin,
and that is the finding rather than an oversight.  The probe applies
`with_vmmaps`, never `m_vmmaps`, and `with_vmmaps h' m` is opened on the
bound `m` before the reading substitutes the fixture: it becomes
`Model.mkModelOf m.m_fd (VmState.mkVmState h' m.m_vm.vmst_lazy
m.m_vm.vmst_materialized) m.m_io …`, so what the fixture lands in is the
raw structure projections `.m_fd`, `.m_vm.vmst_lazy`, `.m_vm.vmst_materialized`,
`.m_io`, … — no `m_vmmaps (opaque_probe h)` for the projection lemma to
match, and no `with_vmmaps h' (opaque_probe h)` for the fold, since the
setter was gone before its argument arrived.  A getter the probe did apply
would fare the same, opened on `m` first.  A fixture registered NEITHER
way behaves exactly as this one does, which is the honest reading of
"projection registration buys nothing under a spec".

`projection_registration_leaves_raw_projections` says what the residue of
the first one IS: the setter was unfolded on the symbolic `m` of the
continuation before the reading put `opaque_probe h` in its place, so the
post-state is a tree of raw projections of `opaque_probe h` with only the
ledger replaced, and the fold never saw a `with_vmmaps h' (opaque_probe h)`.
What that `iff` measures is the ORDER, not the registration: had the fold
matched, the left side would read `opaque_probe h'` against a tree on the
right, which nothing in the set equates, and the pin would fail.  It
cannot tell the two registrations apart, though — `simp` normalizes both
of its sides, so the same statement on the unfolded fixture closes too
(the `example` after it) — and that is why the pair above, not this pin,
is the check on the register.

If a toolchain bump made `sys_norm` close the folded statement under the
projection registration, the `fail_if_success` fails, the header's
argument is up for review, and the projection way is back on the table. -/

def opaque_probe (h : VmMaps) : Model := fixture_of (h := h)

/-- The probe is the registered fixture under another name, so the
registration is the only difference the pins below can see. -/
example (h : VmMaps) : opaque_probe h = fixture_of (h := h) := rfl

/-- The projection of the probe fixture, registered at the default priority.
model: a `rfl` reading of `opaque_probe`'s ledger slot, the projection way
of registering a fixture. -/
@[local sys_simp] theorem m_vmmaps_opaque_probe (h : VmMaps) : m_vmmaps (opaque_probe h) = h := rfl
/-- …and its fold.
model: a `rfl` fold of `with_vmmaps` over `opaque_probe`, the projection
way of registering a fixture. -/
@[local sys_simp] theorem with_vmmaps_opaque_probe (h h' : VmMaps) :
    with_vmmaps h' (opaque_probe h) = opaque_probe h' := rfl

/-- The smallest program that reaches its model through `get_model`: read
it, replace the ledger, answer 0.  Not a spec of anything. -/
def get_model_probe (h' : VmMaps) : Sys SyscallEffect :=
  m <- get_model ;; modify (fun _ => with_vmmaps h' m) ;; Monad.pure (mkEffect 0 [] [])

attribute [local sys_simp low] get_model_probe.eq_1

/-- The residue `sys_norm` leaves on a projection-only fixture: a tree of
raw projections of `opaque_probe h` with the ledger replaced, the fold
never having matched.  What fails it is a reading that substitutes the
model before simplifying the continuation, or a `with_vmmaps` touching a
slot other than the ledger — not the registration (the `example` below).
model: the normal form `sys_norm` produces on `get_model_probe`, a fact
about the tactic and the register, not about Linux. -/
theorem projection_registration_leaves_raw_projections (h h' : VmMaps) (i : SyscallInput)
    (o : outcome SyscallEffect) :
    get_model_probe h' i (opaque_probe h) o ↔
      o = Ok (mkEffect 0 [] [])
             (Model.mkModelOf (opaque_probe h).m_fd
               (VmState.mkVmState h' (opaque_probe h).m_vm.vmst_lazy
                 (opaque_probe h).m_vm.vmst_materialized)
               (opaque_probe h).m_io (opaque_probe h).m_fsys (opaque_probe h).m_proc
               (opaque_probe h).m_lim (opaque_probe h).m_time) [] := by
  sys_norm

/-- The same residue statement on the fixture the register unfolds closes
too: the theorem above measures the reading and the setter, not the
registration. -/
example (h h' : VmMaps) (i : SyscallInput) (o : outcome SyscallEffect) :
    get_model_probe h' i (fixture_of (h := h)) o ↔
      o = Ok (mkEffect 0 [] [])
             (Model.mkModelOf (fixture_of (h := h)).m_fd
               (VmState.mkVmState h' (fixture_of (h := h)).m_vm.vmst_lazy
                 (fixture_of (h := h)).m_vm.vmst_materialized)
               (fixture_of (h := h)).m_io (fixture_of (h := h)).m_fsys (fixture_of (h := h)).m_proc
               (fixture_of (h := h)).m_lim (fixture_of (h := h)).m_time) [] := by
  sys_norm

/-- The same call stated against the FOLDED fixture is not closed by
`sys_norm`; unfolding the fixture is what closes it.
model: the register's reason for unfolding `fixture_of`, a fact about the
tactic and the register, not about Linux. -/
theorem projection_registration_dies_under_get_model (h h' : VmMaps) (i : SyscallInput)
    (o : outcome SyscallEffect) :
    get_model_probe h' i (opaque_probe h) o ↔ o = Ok (mkEffect 0 [] []) (opaque_probe h') [] := by
  fail_if_success (sys_norm; done)
  simp only [opaque_probe.eq_1]
  sys_norm

/-- THE OTHER HALF: the statement `projection_registration_dies_under_get_model`
says `sys_norm` cannot close, closed by `sys_norm` alone on the fixture the
register unfolds — `fixture_of` itself, whose one registration is
`fixture_of.eq_1` at `low`.  Same tactic, same shape; the registration is
the only difference, which is what makes that `fail_if_success` a
measurement rather than a tactic that happened not to fire.
model: the register's first line, a fact about the tactic and the register, not about Linux. -/
theorem unfolding_registration_closes_under_get_model (h h' : VmMaps) (i : SyscallInput)
    (o : outcome SyscallEffect) :
    get_model_probe h' i (fixture_of (h := h)) o ↔ o = Ok (mkEffect 0 [] []) (fixture_of (h := h')) [] := by
  sys_norm

/-! ### The direct reading, where the projection way is alive

`get_model` is not the only reading a spec has: `munmap_spec` reads its
ledger through `get_vmmaps` (`Sys/Mm/Mmap.lean`), and the reading of that
primitive, `bind get_vmmaps k i m o ↔ k (m_vmmaps m) i m o`, hands the
model to the continuation WHOLE — `m_vmmaps m` at the outside of the
continuation, `m` itself under the setter that follows — where
`get_model`'s substitutes it into a continuation already simplified under
its binder.  So the two lemmas `opaque_probe` registers, inert under
`get_model_probe`, both match under `get_vmmaps_probe`: the projection on
`m_vmmaps (opaque_probe h)`, the fold on `with_vmmaps h' (opaque_probe h)`
once `set_vmmaps h'` is read.  `projection_registration_reads_under_get_vmmaps`
pins that the folded statement closes there by `sys_norm`;
`bare_fixture_dies_under_get_vmmaps`, the same statement on `bare_probe`
— `fixture_of` under a name registered NEITHER way — pins that it is the
registration and not the shape that closes it (`fail_if_success`, then
the unfolding).  This is the measurement the header's rule was waiting on:
the projection way works under a direct reading, and the rule stands
because no check runs a symbolic fixture on the one spec that reads that
way. -/

/-- `fixture_of` under a name registered neither way: the control for the
direct-reading pair. -/
def bare_probe (h : VmMaps) : Model := fixture_of (h := h)

/-- The smallest program that reads its ledger DIRECTLY, as `munmap_spec`
does: read it through `get_vmmaps`, replace it, answer its break.  Not a
spec of anything. -/
def get_vmmaps_probe (h' : VmMaps) : Sys SyscallEffect :=
  h <- get_vmmaps ;; set_vmmaps h' ;; Monad.pure (mkEffect h.vm_brk [] [])

attribute [local sys_simp low] get_vmmaps_probe.eq_1

/-- Under the direct reading the projection way is alive: the folded
statement `projection_registration_dies_under_get_model` says `sys_norm`
cannot close under `get_model` closes under `get_vmmaps` on the same
fixture with the same two registrations — the projection reads the break,
the fold folds the post-state.
model: the projection way under a direct reading, a fact about the tactic
and the register, not about Linux. -/
theorem projection_registration_reads_under_get_vmmaps (h h' : VmMaps) (i : SyscallInput)
    (o : outcome SyscallEffect) :
    get_vmmaps_probe h' i (opaque_probe h) o ↔
      o = Ok (mkEffect h.vm_brk [] []) (opaque_probe h') [] := by
  sys_norm

/-- …and it is the registration that closes it: the same statement on
`bare_probe`, registered neither way, is not closed by `sys_norm`, and
unfolding the name is what closes it.
model: the control of the direct-reading pair, a fact about the tactic
and the register, not about Linux. -/
theorem bare_fixture_dies_under_get_vmmaps (h h' : VmMaps) (i : SyscallInput)
    (o : outcome SyscallEffect) :
    get_vmmaps_probe h' i (bare_probe h) o ↔
      o = Ok (mkEffect h.vm_brk [] []) (bare_probe h') [] := by
  fail_if_success (sys_norm; done)
  simp only [bare_probe.eq_1]
  sys_norm

/-- Two fixtures that differ in any slot are different models — the fact a
hand-written refutation of a forged post-state rests on, since `Model`
carries functions and has no decidable equality of its own (`sys_refute`
gets the same from `Model.mkModelOf.injEq` on the unfolded trees, and
needs neither lemma).  Stated as injectivity so one
lemma serves every slot: a forged fd table, ledger, stream, queue or file
system is refuted by the conjunct that reads that slot back. -/
theorem fixture_of_inj {fds fds' : List (word × FdEntry)} {pipes pipes' : List (word × PipeBuf)}
    {h h' : VmMaps} {stdin stdin' : InputStream} {net net' : NetQueue} {fs fs' : Fs.Fs}
    {rlim rlim' utsname utsname' : Option (List byte)}
    (e : fixture_of fds pipes h stdin net fs rlim utsname
           = fixture_of fds' pipes' h' stdin' net' fs' rlim' utsname') :
    fds = fds' ∧ pipes = pipes' ∧ h = h' ∧ stdin = stdin' ∧ net = net' ∧ fs = fs'
      ∧ rlim = rlim' ∧ utsname = utsname' :=
  ⟨congrArg m_fds e, congrArg m_pipes e, congrArg m_vmmaps e, congrArg m_stdin e,
   congrArg m_net e, congrArg m_fs e, congrArg m_rlimit_core e, congrArg m_utsname e⟩

/-! ### `demo_model`: the same readings, and the folds into `fixture_of`

`demo_model_eq_fixture_of` is the check that `fixture_of`'s direct
construction is what `init_model` builds from the demo input — every fixed
field, not only the slots — and a field `init_model` gains fails it.  The
folds are for a check stated on the base itself, whose post-states are
setters applied to `demo_model`. -/

theorem m_fds_demo_model : m_fds demo_model = init_fds := rfl
theorem m_pipes_demo_model : m_pipes demo_model = [] := rfl
theorem m_vmmaps_demo_model : m_vmmaps demo_model = demo_vm := rfl
theorem m_vm_lazy_demo_model : m_vm_lazy demo_model = [] := rfl
theorem m_vm_materialized_demo_model : m_vm_materialized demo_model = [] := rfl
theorem m_stdin_demo_model : m_stdin demo_model = IEof := rfl
theorem m_net_demo_model : m_net demo_model = net_silent := rfl
theorem m_conn_ix_demo_model : m_conn_ix demo_model = Z_to_bv 64 0 := rfl
theorem m_fs_demo_model : m_fs demo_model = [] := rfl
theorem m_halted_demo_model : m_halted demo_model = none := rfl
theorem m_tid_demo_model : m_tid demo_model = none := rfl
theorem m_setsid_succeeded_demo_model : m_setsid_succeeded demo_model = false := rfl
theorem m_has_children_demo_model : m_has_children demo_model = false := rfl
theorem m_sigmask_demo_model : m_sigmask demo_model = Z_to_bv 64 0 := rfl
theorem m_rlimit_core_demo_model : m_rlimit_core demo_model = none := rfl
theorem m_nofile_demo_model : m_nofile demo_model = default_nofile := rfl
theorem m_clock_demo_model : m_clock demo_model = Z_to_bv 64 0 := rfl
theorem m_creds_demo_model : m_creds demo_model = demo_creds := rfl
theorem m_utsname_demo_model : m_utsname demo_model = none := rfl
theorem m_sigaltstack_installed_demo_model : m_sigaltstack_installed demo_model = false := rfl
theorem m_killed_demo_model : m_killed demo_model = none := rfl
theorem m_sigabrt_pending_demo_model : m_sigabrt_pending demo_model = false := rfl
theorem m_abort_terminal_demo_model : m_abort_terminal demo_model = false := rfl
theorem m_statpins_demo_model : m_statpins demo_model = [] := rfl

theorem demo_model_eq_fixture_of : demo_model = fixture_of := rfl

/-- The Rocq call-site shape of a declared /tmp, `init_model …
(demo_input_tmp …)`, IS the fixture form the Lean pins state: the image with
the declaration seeded, at the file-system slot, and the stream at the stdin
slot.  A pin ported from Rocq's `Checks/Cases/Fs/Namei.v` or `Open.v`
rewrites through this rather than hand-seeding a second fixture. -/
theorem init_model_demo_input_tmp_eq_fixture_of (fs0 tmp0 : Fs.Fs) (stdin0 : InputStream) :
    init_model [] 0 0 demo_sp demo_limit (demo_input_tmp fs0 tmp0 stdin0)
      = fixture_of (fs := fs_seed_tmp fs0 tmp0) (stdin := stdin0) := rfl
theorem with_fds_demo_model (fds : List (word × FdEntry)) :
    with_fds fds demo_model = fixture_of (fds := fds) := rfl
theorem with_pipes_demo_model (pipes : List (word × PipeBuf)) :
    with_pipes pipes demo_model = fixture_of (pipes := pipes) := rfl
theorem with_vmmaps_demo_model (h : VmMaps) : with_vmmaps h demo_model = fixture_of (h := h) := rfl
theorem with_vm_backing_nil_demo_model : with_vm_backing [] [] demo_model = demo_model := rfl
theorem with_stdin_demo_model (stdin : InputStream) :
    with_stdin stdin demo_model = fixture_of (stdin := stdin) := rfl
theorem with_net_demo_model (net : NetQueue) : with_net net demo_model = fixture_of (net := net) := rfl
theorem with_fs_demo_model (fs : Fs.Fs) : with_fs fs demo_model = fixture_of (fs := fs) := rfl
theorem with_rlimit_core_demo_model (bs : List byte) :
    with_rlimit_core bs demo_model = fixture_of (rlim := some bs) := rfl
theorem with_utsname_demo_model (bs : List byte) :
    with_utsname bs demo_model = fixture_of (utsname := some bs) := rfl

/-! ## VM ledgers the memory checks run on

Rocq builds each of these but `image_at_4096` as `with_vmmaps <ledger>
(init_model … demo_sp …)` (or, for `noaccess_base`, as a bare `init_model`
under the budget); `image_at_4096` is Lean-only, the image page
`Checks/Cases/Mm/Mmap.lean` reserves for its overlap checks; here they
are `fixture` of a LITERAL ledger, so that a check can state the ledger it
expects to see, and `sys_norm` evaluates the model and the post-state the
spec builds from it to one constructor tree.  The literals are
`mkVmMapsFull` rather than Rocq's `mkVmMaps`, so that the post-state a check
expects and the one the spec builds meet in one normal form without
unfolding `mkVmMaps`'s `Z_to_bv` fields. -/

/-- The demo process with the ledger `h`: `fixture_of` at its VM slot.  The
budget is `h.vm_limit`, and a check that wants one sets it INSIDE the
literal. -/
def fixture (h : VmMaps) : Model := fixture_of (h := h)

-- The second line of the register: `fixture` is a second name for
-- `fixture_of` at its VM slot, and a check that spells a post-state with
-- it needs that name to reach `fixture_of.eq_1`.  Its own `fixture.eq_1`
-- would serve; this `rfl` is the same rewrite under a name that says what
-- it does.
theorem fixture_eq_fixture_of (h : VmMaps) : fixture h = fixture_of (h := h) := rfl
attribute [sys_simp low] fixture_eq_fixture_of

/-- The second line of the register, measured as the first was: the
`fixture h` a check spells its post-state with reaches `fixture_of.eq_1`
through `fixture_eq_fixture_of`, so the folded statement of
`projection_registration_dies_under_get_model` closes on it by `sys_norm`
alone.  Deleting that line fails this, and every `iff` in `Mm/Mmap.lean`
whose post-state is a `fixture` of a symbolic ledger.
model: the register's second line, a fact about the tactic and the register, not about Linux. -/
theorem fixture_reaches_its_unfolding_under_get_model (h h' : VmMaps) (i : SyscallInput)
    (o : outcome SyscallEffect) :
    get_model_probe h' i (fixture h) o ↔ o = Ok (mkEffect 0 [] []) (fixture h') [] := by
  sys_norm
theorem m_vmmaps_fixture (h : VmMaps) : m_vmmaps (fixture h) = h := rfl
theorem m_vm_lazy_fixture (h : VmMaps) : m_vm_lazy (fixture h) = [] := rfl
theorem m_vm_materialized_fixture (h : VmMaps) : m_vm_materialized (fixture h) = [] := rfl
theorem with_vmmaps_fixture (h h' : VmMaps) : with_vmmaps h' (fixture h) = fixture h' := rfl
theorem with_vm_backing_nil_fixture (h : VmMaps) : with_vm_backing [] [] (fixture h) = fixture h := rfl
theorem alloc_top_fixture (h : VmMaps) : alloc_top (m_vmmaps (fixture h)) = alloc_top h := rfl

/-- Two fixtures with different ownership ledgers are different models
(`fixture_of_inj` at the VM slot). -/
theorem fixture_ne_of_maps {h1 h2 : VmMaps} (hne : h1.vm_maps ≠ h2.vm_maps) :
    fixture h1 ≠ fixture h2 :=
  fun e => hne (congrArg VmMaps.vm_maps
    (fixture_of_inj (e : fixture_of (h := h1) = fixture_of (h := h2))).2.2.1)

/-- Every literal ledger below is started at `demo_sp`, so its grant top is
`demo_top`. -/
theorem alloc_top_demo_sp (r m n : List (word × word)) (a b : word) (l : Int) (mb : word) :
    alloc_top (VmMaps.mkVmMapsFull r m n a b l mb demo_sp) = demo_top := by
  simp only [alloc_top, demo_top, bv_unsigned_demo_sp]

/-- One live anonymous rw page at 65536, a 1 GiB budget, nothing reserved. -/
def one_map_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 demo_limit 0 demo_sp)

/-- A live mapping at `addr + n = 2^64 - 4096`, one page short of the word's
end, where the `TASK_SIZE` gate answers before the exact-match arm can see
it.  No real trace ever places a live mapping this close to `2^64` (every
range Linux hands back sits far below `State.alloc_top`), so only a
hand-built model can exercise the gate at its own boundary (the Rocq
`near_ceiling_sum_model` note). -/
def near_ceiling_sum_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (two_pow_64 - 8192), 4096)] [] 0 0 demo_limit 0 demo_sp)

/-- A 16 KiB budget and an empty ledger. -/
def noaccess_base : Model :=
  fixture (VmMaps.mkVmMapsFull [] [] [] 0 0 16384 0 demo_sp)

/-- Three pages owned at 65536 and wholly inaccessible, under a 16 KiB
budget. -/
def noaccess_three_pages : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 12288)] 0 0 16384 0 demo_sp)

/-- A byte the overlay still holds at 65536 after the page there went
inaccessible: what a read through a `PROT_NONE` range must NOT see. -/
def stale_overlay (a : word) : Option byte :=
  if bv_eqb a 65536 then some 42 else none

/-- One byte at 65536 and nothing on either side. -/
theorem stale_overlay_is_one_byte :
    stale_overlay 65535 = none ∧ stale_overlay 65536 = some 42 ∧ stale_overlay 65537 = none := by
  decide

/-- A no-access range at 65536 that NO live mapping owns: the two ledgers
disagreeing, which no grant produces. -/
def noaccess_unowned : Model :=
  fixture (VmMaps.mkVmMapsFull [] [] [(65536, 4096)] 0 0 16384 0 demo_sp)

/-- The image's page at 4096 both reserved and live. -/
def noaccess_image_overlap : Model :=
  fixture (VmMaps.mkVmMapsFull [(4096, 4096)] [(4096, 4096)] [] 0 0 16384 0 demo_sp)

/-- The image reserving the page at 4096, and nothing live. -/
def image_at_4096 : Model :=
  fixture (VmMaps.mkVmMapsFull [(4096, 4096)] [] [] 0 0 16384 0 demo_sp)

/-- One live page at 65536 under a budget of exactly two pages: one more
page grants, a second does not. -/
def tight_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 8192 0 demo_sp)

/-- An empty ledger under the demo budget: the same ledger `demo_model`
starts with, named for the checks about room below the ceiling. -/
def ceiling_room_model : Model := fixture demo_vm

/-- One live page at 131072 under the demo budget, for `region_free`
checks that must be independent of the ceiling and the budget: a grant
immediately ADJACENT to it, `[135168, 139264)`, is disjoint and grants. -/
def region_live_model : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(131072, 4096)] [] 0 0 demo_limit 0 demo_sp)

/-- The map `near_ceiling_sum_model` holds really ends one page short of the
word: the shape the `TASK_SIZE` gate is exercised at. -/
theorem near_ceiling_map_ends_a_page_short :
    bv_unsigned (Z_to_bv 64 (two_pow_64 - 8192)) + 4096 = two_pow_64 - 4096 := by decide

/-! ## User memory a call's arguments point at

`SyscallInput` carries the readable and writable bytes of the process as
`word → Option byte` maps; these are the maps the checks hand it. -/

/-- A byte map answering for exactly the bytes of `bs` laid out from `base`
upward, and `none` everywhere else.  The lower bound is not decoration:
without it every address below `base` subtracts to a negative `Int`, which
`Int.toNat` takes to 0, so the map would answer the FIRST byte of `bs` for
the whole address space below it (`bytes_at_guard_is_load_bearing`). -/
def bytes_at (base : word) (bs : List byte) : word → Option byte :=
  fun a => if bv_unsigned base ≤ bv_unsigned a
           then bs[(bv_unsigned a - bv_unsigned base).toNat]?
           else none

/-- "ab" at 4096, and nothing else readable. -/
def mem_ab : word → Option byte :=
  fun a => if bv_eqb a 4096 then some 97 else if bv_eqb a 4097 then some 98 else none

/-- The writev vector that crosses `MAX_RW_COUNT` inside its second entry:
the first sixteen bytes short of the cap, then 100 and 50 bytes.  What
`cap_iovecs` makes of it — the second entry cut to 16, the third kept at
length 0, the aggregate exactly the cap — is pinned beside `cap_iovecs` in
`Checks/Cases/State.lean`, the subject it pins (ticket A4); Rocq keeps the
Example here. -/
def cap_boundary_iovecs : List (word × word) :=
  [(4096, Z_to_bv 64 (MAX_RW_COUNT - 16)),
   (8192, Z_to_bv 64 100),
   (12288, Z_to_bv 64 50)]

/-- `bytes_at` answers the bytes where they are laid out and nothing past
either end. -/
theorem bytes_at_answers_the_laid_out_bytes :
    bytes_at 4096 [97, 98] 4095 = none ∧ bytes_at 4096 [97, 98] 4096 = some 97
      ∧ bytes_at 4096 [97, 98] 4097 = some 98 ∧ bytes_at 4096 [97, 98] 4098 = none := by decide

/-- THE NEGATIVE: the unguarded map — the same lookup without the lower
bound — answers the first byte one below `base`, which is what the guard is
there to refuse. -/
theorem bytes_at_guard_is_load_bearing :
    (fun a : word => ([97, 98] : List byte)[(bv_unsigned a - bv_unsigned (4096 : word)).toNat]?) 4095
      = some 97 := by decide

/-- `mem_ab` is "ab" at 4096 and unreadable on both sides. -/
theorem mem_ab_is_ab_at_4096 :
    mem_ab 4095 = none ∧ mem_ab 4096 = some 97 ∧ mem_ab 4097 = some 98 ∧ mem_ab 4098 = none := by
  decide

/-! ## fd tables and file systems: a file written past its end -/

/-- A file "hi" at path `[102]`, held for writing through fd 3 at offset 4,
past the file's end, and the fd table is only fd 3 as in Rocq: no standard
channel.  Rocq spells this through `mkModel`, which leaves `mkModel`'s
overflow credentials in place; here the credentials are the demo user's.
That is harmless while every pin on `wpast_model` is a `write` or `read`
arm, which read no credentials; a pin that reaches an arm reading `m_creds`
must spell the overflow credentials with `with_creds` first. -/
def wpast_model : Model :=
  fixture_of (fds := [(3, .FdFileW [102] 4)]) (fs := [([102], [104, 105])])

/-! ## prlimit64 (261): the RLIMIT_CORE record and its landing zones -/

/-- A `struct rlimit64` as its sixteen little-endian bytes: `soft` and
`hard` each in the low byte of their eight. -/
def rlim_bytes (soft hard : byte) : List byte :=
  [soft, 0, 0, 0, 0, 0, 0, 0, hard, 0, 0, 0, 0, 0, 0, 0]

/-- A writable 16-byte landing zone at 4096 for the read's out-parameter. -/
def rlim_out : word → Option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4112 then some 0 else none

/-- A readable source struct at 8192, for the set arm. -/
def rlim_src_at (soft hard : byte) : word → Option byte :=
  fun a => if bv_ltu a 8192 then none
           else if bv_eqb a 8192 then some soft
           else if bv_ltu a 8200 then some 0
           else if bv_eqb a 8200 then some hard
           else if bv_ltu a 8208 then some 0
           else none

/-- A NONZERO soft limit on purpose: it is what lets a set actually change
the record, so a read-after-set check cannot pass by accident. -/
def rlim_pinned : Model := fixture_of (rlim := some (rlim_bytes 3 7))

/-- The source struct is `rlim_bytes soft hard` laid out at 8192 and nothing
outside its sixteen bytes — the two spellings agree byte for byte. -/
theorem rlim_src_at_is_rlim_bytes_at_8192 :
    (List.range 18).all (fun k =>
      rlim_src_at 3 7 (Z_to_bv 64 (8191 + k)) = bytes_at 8192 (rlim_bytes 3 7) (Z_to_bv 64 (8191 + k)))
    = true := by decide

/-- The landing zone is exactly sixteen bytes. -/
theorem rlim_out_is_sixteen_bytes :
    rlim_out 4095 = none ∧ rlim_out 4096 = some 0 ∧ rlim_out 4111 = some 0 ∧ rlim_out 4112 = none := by
  decide

/-! ## uname (160): the landing zones and the wrapped name -/

/-- A 390-byte writable landing zone at 4096 for `uname`'s only
out-parameter.  Deliberately EXACT: `uts_out_short` is the same zone one
byte shy, which is the shape that separates the -EFAULT arm from the
decline. -/
def uts_out : word → Option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4486 then some 0 else none

def uts_out_short : word → Option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4485 then some 0 else none

/-- "6.18.46" and "6.1.0" — two RELEASE strings, both inside the envelope.
Which one a machine reports is not something the kernel source settles, so
neither is privileged; what the uname checks use them for is that a run may
report one of them and then must go on reporting THAT one. -/
def uts_release_a : List Int := [54, 46, 49, 56, 46, 52, 54]
def uts_release_b : List Int := [54, 46, 49, 46, 48]

/-- The last four bytes of the address space, so the 390-byte copy-out
covers them and then 386 more at 0 — the shape `State.read_bytes_map`'s
wrapping walk accepts and `State.access_okb`'s `Int` subtraction refuses. -/
def uts_wrap_name : word := Z_to_bv 64 (2 ^ 64 - 4)

def uts_wrap_mem : word → Option byte :=
  fun a => if bv_unsigned a < 386 ∨ 2 ^ 64 - 4 ≤ bv_unsigned a
           then some (Z_to_bv 8 0) else none

/-- The two zones differ in exactly their last byte: 4485 is inside the
full one and outside the short one. -/
theorem uts_out_short_is_one_byte_shy :
    uts_out 4485 = some 0 ∧ uts_out_short 4485 = none
      ∧ uts_out 4486 = none ∧ uts_out_short 4484 = some 0 := by decide

/-- The wrapped zone is the last four bytes and the first 386, and nothing
between. -/
theorem uts_wrap_mem_is_the_two_ends :
    uts_wrap_mem uts_wrap_name = some (Z_to_bv 8 0) ∧ uts_wrap_mem (Z_to_bv 64 385) = some (Z_to_bv 8 0)
      ∧ uts_wrap_mem (Z_to_bv 64 386) = none ∧ uts_wrap_mem (Z_to_bv 64 (2 ^ 64 - 5)) = none := by
  decide

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude

open Lean Elab Command in
/-- The register this file exports is exactly the two lines its header
names, `fixture_of.eq_1` and `fixture_eq_fixture_of`.  Read off the
`sys_simp` set after the namespace has closed, so the `local` registrations
of the probe fixtures above are out of scope: a projection or fold lemma on
`fixture_of` or `fixture` registered for export — the way `Tactic.lean`'s
header calls opaque, dead under `get_model` — fails this file's build
naming it, and so does a register line that has gone missing. -/
elab "#check_prelude_register" : command => do
  let some ext ← liftCoreM (Meta.getSimpExtension? `sys_simp)
    | throwError "sys_simp is not registered"
  let thms ← liftCoreM ext.getTheorems
  let here := `LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
  let members := thms.lemmaNames.fold (init := (#[] : Array Name)) fun acc o =>
    match o with
    | .decl n _ _ => if here.isPrefixOf n then acc.push n else acc
    | _ => acc
  let wanted : Array Name := #[here ++ `fixture_of.eq_1, here ++ `fixture_eq_fixture_of]
  let extra := members.filter (fun n => !wanted.contains n)
  let missing := wanted.filter (fun n => !members.contains n)
  unless extra.isEmpty do
    throwError "sys_simp holds a member of Checks.Cases.Prelude its header does not name: {extra}"
  unless missing.isEmpty do
    throwError "sys_simp is missing a register line of Checks.Cases.Prelude: {missing}"

#check_prelude_register
