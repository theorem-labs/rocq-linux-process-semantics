import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
import LinuxProcessSemantics.LinuxProcessSem.StackLayout
import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei

/-! rocq-baseline: 9f9a96b29a12dd26b54bff74b47ba1c4a6e01ad3 -/

/-! # LinuxProcessSem.Run — Kleene-star trace semantics

Mirrors `theories/LinuxProcessSem/Run.v` at the header's baseline, name for
name.  First read at 9a070af9e60b69831eee66067be0dd42e5ec244e, and brought to
f44244ad by ticket A12: the killed terminal rule (`sstep_killed`), the
kill-freedom of the exit rule, and the declaration-off frame
(`decl_off_frame` and what it yields).  The four run-semantics twins name
the day tip as their baseline rather than f44244ad, where the ticket read
them: `State.v`, which their closures reach (`ProcInput`, `IoState`,
`FdEntry`), moved at #712 (the random device), and `Run.v` itself at #818
(the task-declared AT_HWCAP word, whose default-stance pair
`valid_input_hwcap_rv64gc`/`rv64gcv` is ported below), so a baseline before
either reports those changes as this twin's drift.  Ticket K10-prereq-run
read it at 8fe98f0af: the two commits there after 7b4cf4958, #1217 and
#1235, changed proofs and added the by-name `valid_input` accessors, and no
definition.

TRUST BOUNDARY: this file is part of the trusted specification.

A binary's observable behavior is its set of finite trace prefixes plus
TWO error facts: whether SOME execution can reach the explicit error
transition (`reaches_error`), and whether ALL executions must reach it
(`all_traces_error`) — and a coverage fact, `reaches_unmodeled`: whether
the run can reach a configuration where THIS MODEL gave up, as opposed to
one where the PROGRAM died.

Rocq's section variables (`mi_loaded_segments`, `mi_init_pc`, …) are
explicit arguments here, in the order Rocq abstracts them, so `sstep segs
c evs st` and `init_config segs pc ph sp brk0 mbase rnd lim inp` read the
same in both.

THE SPURIOUS-FAILURE CONFIGURATION AND THE ABORT STANCE were held out of
this file while nothing in the Lean tree could read them — a step relation
nothing reads is a claim nothing checks — and came in with ticket
K10-prereq-run, for `Checks/BudgetPremise` (ticket K10): the statements that
file proves are Rocq's budget families of `Equivalence.v`, which quantify
over a `SpuriousCfg` and over `valid_input_abort`; a Lean statement
without them would say less than the Rocq one it mirrors.
`Checks/SpuriousCfg.lean` pins the filter on hand-chosen cases, in both
directions.  `valid_input_abort` waited on something else as well: it
quantifies over runs in which a SIGABRT the process sends itself ends it,
the work of the tkill (130)/tgkill (131) arms, and ported ahead of them it
would have described runs the Lean model did not produce.  Both arms are in
the Lean table now (`Sys/Kernel/Signal.lean`); the pilot still uses
`valid_input`, which pins the declaration false, and `lean/README.md`
states the correspondence boundary. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Run

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem (reg_get)
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall (w_is0)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
  (brk_budget_refused_b mmap_budget_refused_b min_brk mmap_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap (mremap_budget_refused_b mremap_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect (mprotect_budget_refused_b mprotect_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.DPath (getcwd_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File (dup_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open (faccessat_errnos openat_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Pipe (pipe2_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sys (setid_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork (clone_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket
  (socket_errnos socketpair_reserve_errnos socketpair_create_errnos bind_errnos
   listen_errnos accept_errnos)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Drivers.Char.Random (getrandom_errnos)

/-! ## Trace prefixes and observable behaviors -/

def is_prefix {A : Type} (l1 l2 : List A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x = y ∧ is_prefix xs ys

theorem is_prefix_refl {A : Type} (l : List A) : is_prefix l l := by
  induction l with
  | nil => trivial
  | cons x xs ih => exact ⟨rfl, ih⟩

theorem is_prefix_nil {A : Type} (l : List A) : is_prefix [] l := by
  cases l <;> trivial

theorem is_prefix_trans {A : Type} (l1 l2 l3 : List A) :
    is_prefix l1 l2 → is_prefix l2 l3 → is_prefix l1 l3 := by
  induction l1 generalizing l2 l3 with
  | nil => intros; exact is_prefix_nil _
  | cons x xs ih =>
    cases l2 with
    | nil => intro h; exact absurd h id
    | cons y ys =>
      cases l3 with
      | nil => intro _ h; exact absurd h id
      | cons z zs =>
        rintro ⟨rfl, h1⟩ ⟨rfl, h2⟩
        exact ⟨rfl, ih ys zs h1 h2⟩

theorem is_prefix_app {A : Type} (l1 l2 : List A) : is_prefix l1 (l1 ++ l2) := by
  induction l1 with
  | nil => exact is_prefix_nil _
  | cons x xs ih => exact ⟨rfl, ih⟩

/-- Everything observable about one binary on one input. -/
structure behavior where
  mkBehavior ::
  bh_traces : List event → Prop
  bh_errors : Prop
  bh_all_errors : Prop
  bh_unmodeled : Prop

/-! ## Applying a chosen syscall effect to the machine -/

/-- The decoded syscall argument registers a0..a5 at the `ecall`. -/
def syscall_args (ms : machine_state) : List word :=
  [ms_gpr ms 0, ms_gpr ms 1, ms_gpr ms 2, ms_gpr ms 3, ms_gpr ms 4, ms_gpr ms 5]

def apply_writes (mem : word → Option byte) (ws : List (word × List byte))
    : word → Option byte :=
  match ws with
  | [] => mem
  | (a, bs) :: r => apply_writes (write_to_mem mem a bs) r

/-- Is `a` inside one of the (base, size) ranges? -/
def zeros_cover (zs : List (word × word)) (a : word) : Bool :=
  zs.any (fun z => bv_unsigned z.1 ≤ bv_unsigned a
                   && bv_unsigned a < bv_unsigned z.1 + bv_unsigned z.2)

/-- Zero-fill the effect's granted ranges. -/
def apply_zeros (mem : word → Option byte) (zs : List (word × word))
    : word → Option byte :=
  match zs with
  | [] => mem
  | _ => fun a => if zeros_cover zs a then some (Z_to_bv 8 0) else mem a

/-- Erase the effect's inaccessible ranges. -/
def apply_unmaps (mem : word → Option byte) (us : List (word × word))
    : word → Option byte :=
  match us with
  | [] => mem
  | _ => fun a => if zeros_cover us a then none else mem a

/-- Apply a symbolic copy against an immutable snapshot of the memory from
BEFORE this syscall effect. -/
def apply_copy (before mem : word → Option byte) (c : MemCopy) : word → Option byte :=
  fun a =>
    if bv_unsigned c.copy_dst ≤ bv_unsigned a
       && bv_unsigned a < bv_unsigned c.copy_dst + bv_unsigned c.copy_len
    then before (Z_to_bv 64
           (bv_unsigned c.copy_src + (bv_unsigned a - bv_unsigned c.copy_dst)))
    else mem a

def apply_copies (before mem : word → Option byte) (cs : List MemCopy)
    : word → Option byte :=
  match cs with
  | [] => mem
  | c :: r => apply_copies before (apply_copy before mem c) r

/-- Apply a chosen effect: set a0, erase the unmapped ranges, zero-fill the
granted ranges, copy preserved bytes from the snapshot, write the declared
ranges.  Everything else is preserved BY CONSTRUCTION. -/
def apply_effect (ms : machine_state) (eff : SyscallEffect) : machine_state :=
  let ms' := set_reg ms 10 eff.eff_ret
  { ms' with
    ms_mem := apply_writes
                (apply_copies ms'.ms_mem
                  (apply_zeros (apply_unmaps ms'.ms_mem eff.eff_unmaps)
                               eff.eff_zeros)
                  eff.eff_copies)
                eff.eff_writes }

/-- Advance PC past the ecall instruction (+4) and clear svc_pending. -/
def advance_past_svc (ms : machine_state) : machine_state :=
  { ms with ms_pc_val := ms_pc ms + Z_to_bv 64 4, ms_svc_pending := none }

/-! ## Configurations and the one-step relation -/

structure config where
  mkCfg ::
  cfg_ms    : machine_state
  cfg_model : Model

/-- The address space the kernel already used at `execve`: each LOAD
segment, PAGE-ROUNDED. -/
def segment_reservation (s : Segment) : word × word :=
  let lo := page_round_down_Z (s.seg_base : Int)
  let hi := page_round_up_Z ((s.seg_base : Int) + s.seg_size)
  (Z_to_bv 64 lo, Z_to_bv 64 (hi - lo))

def segments_reserved (segs : List Segment) : List (word × word) :=
  segs.map segment_reservation

/-- Where a step can go: on to another configuration, or the explicit
error transition. -/
inductive step_to : Type
  | SNext (c : config)
  | SError

export step_to (SNext SError)

section WithMemImage

variable (mi_loaded_segments : List Segment)

/-- Execute one instruction and atomically charge every newly touched page
in a lazy anonymous reservation. -/
def mi_account_step (ms : machine_state) (model : Model)
    : machine_result (machine_state × Model) :=
  match step_accesses mi_loaded_segments ms with
  | MachineOk report =>
      match materialize_model_accesses model report.accessed_ranges with
      | some model' => MachineOk (report.access_value, model')
      | none => MachineFault
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled

/-- Accounting is an overlay on the authoritative instruction semantics. -/
theorem mi_account_step_projects (ms : machine_state) (model : Model)
    (ms' : machine_state) (model' : Model) :
    mi_account_step mi_loaded_segments ms model = MachineOk (ms', model') →
    step mi_loaded_segments ms = MachineOk ms' := by
  intro h
  unfold mi_account_step at h
  unfold step drop_access_report
  cases hs : step_accesses mi_loaded_segments ms with
  | MachineOk report =>
    simp only [hs] at h
    cases hm : materialize_model_accesses model report.accessed_ranges with
    | none => simp [hm] at h
    | some accounted =>
      simp only [hm, machine_result.MachineOk.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | MachineFault => simp [hs] at h
  | MachineUnmodeled => simp [hs] at h

theorem mi_account_step_model_frame (ms : machine_state) (model : Model)
    (ms' : machine_state) (model' : Model) :
    mi_account_step mi_loaded_segments ms model = MachineOk (ms', model') →
    model'.m_fd = model.m_fd ∧
    m_vmmaps model' = m_vmmaps model ∧
    m_vm_lazy model' = m_vm_lazy model ∧
    model'.m_io = model.m_io ∧
    model'.m_fsys = model.m_fsys ∧
    model'.m_proc = model.m_proc ∧
    model'.m_lim = model.m_lim := by
  intro h
  unfold mi_account_step at h
  cases hs : step_accesses mi_loaded_segments ms with
  | MachineOk report =>
    simp only [hs] at h
    cases hm : materialize_model_accesses model report.accessed_ranges with
    | none => simp [hm] at h
    | some accounted =>
      simp only [hm, machine_result.MachineOk.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact materialize_model_accesses_frame model report.accessed_ranges accounted hm
  | MachineFault => simp [hs] at h
  | MachineUnmodeled => simp [hs] at h

/-- With no lazy mappings there is nothing to charge. -/
theorem mi_account_step_no_lazy (ms : machine_state) (model : Model) :
    m_vm_lazy model = [] →
    mi_account_step mi_loaded_segments ms model =
      match step mi_loaded_segments ms with
      | MachineOk ms' => MachineOk (ms', model)
      | MachineFault => MachineFault
      | MachineUnmodeled => MachineUnmodeled := by
  intro hlazy
  unfold mi_account_step step drop_access_report
  cases step_accesses mi_loaded_segments ms with
  | MachineOk report =>
    simp only
    rw [materialize_model_accesses_no_lazy model report.accessed_ranges hlazy]
  | MachineFault => rfl
  | MachineUnmodeled => rfl

/-- The input handed to the syscall spec. -/
def sys_input (ms : machine_state) (x8 : word) : SyscallInput :=
  SyscallInput.mkInput x8 (syscall_args ms) (ms_read_byte ms)
          (ms_writable_byte mi_loaded_segments ms)

/-- One transition. -/
inductive sstep : config → List event → step_to → Prop
  | sstep_instr : ∀ ms model ms' model',
      m_halted model = none →
      ms.ms_svc_pending = none →
      mi_account_step mi_loaded_segments ms model = MachineOk (ms', model') →
      sstep (config.mkCfg ms model) [] (SNext (config.mkCfg ms' model'))
  | sstep_instr_fault : ∀ ms model,
      m_halted model = none →
      ms.ms_svc_pending = none →
      mi_account_step mi_loaded_segments ms model = MachineFault →
      sstep (config.mkCfg ms model) [] SError
  | sstep_instr_unmodeled : ∀ ms model,
      m_halted model = none →
      ms.ms_svc_pending = none →
      mi_account_step mi_loaded_segments ms model = MachineUnmodeled →
      sstep (config.mkCfg ms model) [] SError
  | sstep_syscall : ∀ ms model x8 eff model' model'' evs,
      m_halted model = none →
      ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input mi_loaded_segments ms x8) model (Ok eff model' evs) →
      m_halted model' = none →
      materialize_model_accesses model' (syscall_effect_accesses eff) = some model'' →
      sstep (config.mkCfg ms model) evs
            (SNext (config.mkCfg (advance_past_svc (apply_effect ms eff)) model''))
  | sstep_syscall_materialization_fault : ∀ ms model x8 eff model' evs,
      m_halted model = none →
      ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input mi_loaded_segments ms x8) model (Ok eff model' evs) →
      m_halted model' = none →
      materialize_model_accesses model' (syscall_effect_accesses eff) = none →
      sstep (config.mkCfg ms model) [] SError
  | sstep_exit : ∀ ms model x8 eff model' evs code,
      m_halted model = none →
      ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input mi_loaded_segments ms x8) model (Ok eff model' evs) →
      m_halted model' = some code →
      m_killed model' = none →
      sstep (config.mkCfg ms model) (evs ++ [ExitEv code (m_fs model')])
            (SNext (config.mkCfg ms model'))
  /-- The other way a process ends: a fatal signal it sent itself.  Same
  shape as `sstep_exit` and the same discarded effect — the syscall
  completes in the kernel and the process is killed on the return to
  user space (`get_signal`, kernel/signal.c, Linux v6.18.46, commit
  1f99e9ab748f, → `do_group_exit`, kernel/exit.c, same version), so what
  it wrote to its own memory is never read — and the two arms are
  disjoint by `m_killed`, which `sstep_exit` requires to be `none`.  The
  task's declaration is NOT a premise here.  In Rocq the `tkill`/`tgkill`
  arms test `m_abort_terminal` before they reach `send_sigabrt`
  (`Sys/Kernel/Signal.v`), the writer of `State.m_killed`; the second
  writer, the pending-SIGABRT delivery `rt_sigprocmask` runs through
  `sigmask_deliver_model`, is gated on `m_sigabrt_pending` instead, which
  only `send_sigabrt` sets.  Repeating the declaration here would leave a
  configuration STUCK on an outcome the spec layer produced rather than
  declined.  What carries the compatibility claim, and why the second
  writer's gate matters to it, is `decl_off_frame` below.  (Rocq:
  `Run.sstep_killed`.) -/
  | sstep_killed : ∀ ms model x8 eff model' evs sig,
      m_halted model = none →
      ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input mi_loaded_segments ms x8) model (Ok eff model' evs) →
      m_killed model' = some sig →
      sstep (config.mkCfg ms model) (evs ++ [KillEv sig (m_fs model')])
            (SNext (config.mkCfg ms model'))
  | sstep_syscall_unmodeled : ∀ ms model x8,
      m_halted model = none →
      ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input mi_loaded_segments ms x8) model Unmodeled →
      sstep (config.mkCfg ms model) [] SError

/-- Kleene star of `sstep`, accumulating events. -/
inductive star : config → List event → config → Prop
  | star_refl : ∀ c, star c [] c
  | star_step : ∀ c1 evs c2 tr c3,
      sstep mi_loaded_segments c1 evs (SNext c2) →
      star c2 tr c3 →
      star c1 (evs ++ tr) c3

theorem star_one (c : config) (evs : List event) (c' : config) :
    sstep mi_loaded_segments c evs (SNext c') → star mi_loaded_segments c evs c' := by
  intro h
  have := star.star_step c evs c' [] c' h (star.star_refl c')
  simpa using this

theorem star_trans (c1 : config) (t1 : List event) (c2 : config) (t2 : List event) (c3 : config) :
    star mi_loaded_segments c1 t1 c2 → star mi_loaded_segments c2 t2 c3 →
    star mi_loaded_segments c1 (t1 ++ t2) c3 := by
  intro h1
  induction h1 generalizing t2 c3 with
  | star_refl c => intro h2; simpa using h2
  | star_step c1 evs c2 tr c3' hs _ ih =>
    intro h2
    rw [List.append_assoc]
    exact star.star_step _ _ _ _ _ hs (ih t2 c3 h2)

/-! ## Observable behavior -/

/-- `tr` is an event-level prefix of an admissible run. -/
def obs_trace (c0 : config) (tr : List event) : Prop :=
  ∃ tr' c, star mi_loaded_segments c0 tr' c ∧ is_prefix tr tr'

theorem obs_trace_nil (c0 : config) : obs_trace mi_loaded_segments c0 [] :=
  ⟨[], c0, star.star_refl c0, is_prefix_nil _⟩

theorem obs_trace_prefix_closed (c0 : config) (tr tr' : List event) :
    obs_trace mi_loaded_segments c0 tr → is_prefix tr' tr → obs_trace mi_loaded_segments c0 tr' := by
  rintro ⟨tr'', c, hstar, hp⟩ hp'
  exact ⟨tr'', c, hstar, is_prefix_trans _ _ _ hp' hp⟩

/-! ## The declaration off is the old semantics: what that rests on

`State.in_abort_terminal` is meant to be inert when it is `false`: a run
whose task did not declare the abort path should produce exactly the
traces, errors and uncovered points it produced before `tkill` had an
arm.  Two of the three things that has to mean are facts about the SPEC
LAYER — that no arm turns the declaration on, records a kill under it,
or emits a `KillEv` of its own — and this development has no lemma
quantified over the arms of the table to prove them with.  So they are a
hypothesis with a name, `decl_off_frame`, stated as an INVARIANT and not
a one-sided frame: the delivery inside `rt_sigprocmask` branches on the
pending bit, not on the declaration, so a model with the declaration
clear and the pending bit set is killed by an ordinary
`rt_sigprocmask(SIG_UNBLOCK, {SIGABRT})`.  The hypothesis therefore
carries `m_sigabrt_pending` and the conclusion re-establishes it, and
`State.init_model`, which clears both, is the base case.  The full
argument, and the one-sided form's refutation, are on the Rocq
definitions (`Run.decl_off_frame`,
`Checks.Cases.Kernel.Signal.decl_off_frame_one_sided_refuted`). -/

def decl_off_frame : Prop :=
  ∀ i m eff m' evs,
    syscall_spec i m (Ok eff m' evs) →
    m_abort_terminal m = false →
    m_sigabrt_pending m = false →
    m_abort_terminal m' = false
    ∧ m_sigabrt_pending m' = false
    ∧ m_killed m' = none
    ∧ (∀ sig fs, ¬ KillEv sig fs ∈ evs)

/-- The form `decl_off_frame` had before.  It is FALSE — a model with the
declaration clear and the pending bit set is killed by an ordinary
`rt_sigprocmask(SIG_UNBLOCK, {SIGABRT})` — so nothing may consume it: a
theorem stated with it as a hypothesis is vacuous.  Rocq keeps it only so
that `Checks.Cases.Kernel.Signal.decl_off_frame_one_sided_refuted` has
something to refute; that refutation runs the `rt_sigprocmask` delivery
path (`sigmask_deliver_model`), and Lean carries it under the same name in
`Checks/Cases/Kernel/Signal.lean`.  (Rocq: `Run.decl_off_frame_one_sided`.) -/
def decl_off_frame_one_sided : Prop :=
  ∀ i m eff m' evs,
    syscall_spec i m (Ok eff m' evs) →
    m_abort_terminal m = false →
    m_abort_terminal m' = false
    ∧ m_killed m' = none
    ∧ (∀ sig fs, ¬ KillEv sig fs ∈ evs)

theorem m_abort_terminal_proc (m1 m2 : Model) :
    m1.m_proc = m2.m_proc → m_abort_terminal m1 = m_abort_terminal m2 := by
  intro h
  unfold m_abort_terminal
  rw [h]

theorem m_sigabrt_pending_proc (m1 m2 : Model) :
    m1.m_proc = m2.m_proc → m_sigabrt_pending m1 = m_sigabrt_pending m2 := by
  intro h
  unfold m_sigabrt_pending
  rw [h]

/-- One step, with the declaration off and nothing pending: BOTH bits
stay clear, and the events the step contributes carry no kill.  The
pending bit is carried for the reason the frame carries it. -/
theorem sstep_off_no_kill (hframe : decl_off_frame) (ms : machine_state) (model : Model)
    (evs : List event) (c' : config) :
    m_abort_terminal model = false →
    m_sigabrt_pending model = false →
    sstep mi_loaded_segments (config.mkCfg ms model) evs (SNext c') →
    m_abort_terminal c'.cfg_model = false
    ∧ m_sigabrt_pending c'.cfg_model = false
    ∧ (∀ sig fs, ¬ KillEv sig fs ∈ evs) := by
  intro hoff hpend hstep
  cases hstep with
  | sstep_instr _ _ ms' model' _ _ hacc =>
    -- an instruction: accounting keeps `State.m_proc` fixed
    obtain ⟨_, _, _, _, _, hproc, _⟩ := mi_account_step_model_frame mi_loaded_segments _ _ _ _ hacc
    refine ⟨?_, ?_, fun _ _ h => nomatch h⟩
    · show m_abort_terminal model' = false
      rw [← hoff]; exact m_abort_terminal_proc _ _ hproc
    · show m_sigabrt_pending model' = false
      rw [← hpend]; exact m_sigabrt_pending_proc _ _ hproc
  | sstep_syscall _ _ x8 eff model' model'' evs1 _ _ hspec _ hmat =>
    -- a syscall that materializes: the frame, then materialization,
    -- which keeps `State.m_proc` fixed too
    obtain ⟨hoff', hpend', _, hev⟩ := hframe _ _ _ _ _ hspec hoff hpend
    obtain ⟨_, _, _, _, _, hproc, _⟩ := materialize_model_accesses_frame _ _ _ hmat
    refine ⟨?_, ?_, hev⟩
    · show m_abort_terminal model'' = false
      rw [← hoff']; exact m_abort_terminal_proc _ _ hproc
    · show m_sigabrt_pending model'' = false
      rw [← hpend']; exact m_sigabrt_pending_proc _ _ hproc
  | sstep_exit _ _ x8 eff model' evs1 code _ _ hspec _ _ =>
    -- exit: the effect is discarded, so the post-model is the spec's
    obtain ⟨hoff', hpend', _, hev⟩ := hframe _ _ _ _ _ hspec hoff hpend
    refine ⟨hoff', hpend', ?_⟩
    intro sig fs hin
    rcases List.mem_append.1 hin with hin | hin
    · exact hev sig fs hin
    · exact event.noConfusion (List.mem_singleton.1 hin)
  | sstep_killed _ _ x8 eff model' evs1 sig _ _ hspec hk =>
    -- kill: the frame says no arm records one from a state with both bits clear
    obtain ⟨_, _, hk', _⟩ := hframe _ _ _ _ _ hspec hoff hpend
    rw [hk'] at hk
    cases hk

/-- In a whole execution, the same.  `State.init_model` clears both bits
(`State.m_sigabrt_pending_init_model`; `State.m_abort_terminal_init_model`
reads the declaration off the input), so a run whose task did not declare
the abort path meets this lemma's hypotheses at its first configuration. -/
theorem star_off_no_kill (hframe : decl_off_frame) (c : config) (tr : List event) (c' : config) :
    m_abort_terminal c.cfg_model = false →
    m_sigabrt_pending c.cfg_model = false →
    star mi_loaded_segments c tr c' →
    ∀ sig fs, ¬ KillEv sig fs ∈ tr := by
  intro hoff hpend hstar
  revert hoff hpend
  induction hstar with
  | star_refl c => exact fun _ _ _ _ h => nomatch h
  | star_step c1 evs c2 tr c3 hstep _ ih =>
    intro hoff hpend
    rcases c1 with ⟨ms, model⟩
    obtain ⟨hoff', hpend', hev⟩ :=
      sstep_off_no_kill mi_loaded_segments hframe ms model evs c2 hoff hpend hstep
    intro sig fs hin
    rcases List.mem_append.1 hin with hin | hin
    · exact hev sig fs hin
    · exact ih hoff' hpend' sig fs hin

theorem in_is_prefix {A : Type} (x : A) (l1 l2 : List A) :
    is_prefix l1 l2 → x ∈ l1 → x ∈ l2 := by
  induction l1 generalizing l2 with
  | nil => intro _ h; exact nomatch h
  | cons a l1 ih =>
    cases l2 with
    | nil => intro hp; exact absurd hp id
    | cons b l2 =>
      rintro ⟨rfl, hp⟩ hin
      rcases List.mem_cons.1 hin with rfl | hin
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons.2 (Or.inr (ih l2 hp hin))

/-- The run can take the explicit error transition. -/
def reaches_error (c0 : config) : Prop :=
  ∃ tr c evs, star mi_loaded_segments c0 tr c ∧ sstep mi_loaded_segments c evs SError

/-! ## Coverage: where the MODEL gives up, as opposed to where the PROGRAM dies

The argument for what is and is not included — above all why
`MachineFault` is deliberately NOT here, and the two premises about signal
dispositions and signal delivery that exclusion rests on — is on the Rocq
definition. -/
def unmodeled_at (c : config) : Prop :=
  m_halted c.cfg_model = none ∧
  ( (c.cfg_ms.ms_svc_pending = none ∧
       mi_account_step mi_loaded_segments c.cfg_ms c.cfg_model = MachineUnmodeled)
    ∨ (∃ x8, c.cfg_ms.ms_svc_pending = some x8 ∧
             syscall_spec (sys_input mi_loaded_segments c.cfg_ms x8) c.cfg_model Unmodeled) )

/-- The run can reach a configuration the model does not cover. -/
def reaches_unmodeled (c0 : config) : Prop :=
  ∃ tr c, star mi_loaded_segments c0 tr c ∧ unmodeled_at mi_loaded_segments c

theorem unmodeled_at_sstep_error (c : config) :
    unmodeled_at mi_loaded_segments c → ∃ evs, sstep mi_loaded_segments c evs SError := by
  rcases c with ⟨ms, model⟩
  rintro ⟨hh, (⟨hsvc, hstep⟩ | ⟨x8, hsvc, hspec⟩)⟩
  · exact ⟨[], sstep.sstep_instr_unmodeled _ _ hh hsvc hstep⟩
  · exact ⟨[], sstep.sstep_syscall_unmodeled _ _ x8 hh hsvc hspec⟩

theorem reaches_unmodeled_reaches_error (c0 : config) :
    reaches_unmodeled mi_loaded_segments c0 → reaches_error mi_loaded_segments c0 := by
  rintro ⟨tr, c, hstar, hun⟩
  obtain ⟨evs, hss⟩ := unmodeled_at_sstep_error mi_loaded_segments c hun
  exact ⟨tr, c, evs, hstar, hss⟩

theorem no_error_no_unmodeled (c0 : config) :
    ¬ reaches_error mi_loaded_segments c0 → ¬ reaches_unmodeled mi_loaded_segments c0 :=
  fun h hun => h (reaches_unmodeled_reaches_error mi_loaded_segments c0 hun)

/-- NON-VACUITY: every machine state the step function declines is a
witness, reached in zero steps. -/
theorem reaches_unmodeled_intro (ms : machine_state) (model : Model) :
    m_halted model = none →
    ms.ms_svc_pending = none →
    mi_account_step mi_loaded_segments ms model = MachineUnmodeled →
    reaches_unmodeled mi_loaded_segments (config.mkCfg ms model) :=
  fun hh hsvc hstep =>
    ⟨[], config.mkCfg ms model, star.star_refl _, hh, Or.inl ⟨hsvc, hstep⟩⟩

/-- Every maximal execution from `c0` reaches the explicit error
transition after finitely many steps.  Inductive, with a progress premise
(no stuck configuration passes vacuously) and a recursive premise over
EVERY `SNext` successor. -/
inductive all_traces_error : config → Prop
  | all_traces_error_intro : ∀ c,
      (∃ evs to, sstep mi_loaded_segments c evs to) →
      (∀ evs c', sstep mi_loaded_segments c evs (SNext c') → all_traces_error c') →
      all_traces_error c

theorem all_traces_error_reaches_error (c : config) :
    all_traces_error mi_loaded_segments c → reaches_error mi_loaded_segments c := by
  intro hall
  induction hall with
  | all_traces_error_intro c hprog _ ih =>
    obtain ⟨evs, to, hstep⟩ := hprog
    cases to with
    | SNext c' =>
      obtain ⟨tr, c2, err_evs, hstar, herr⟩ := ih evs c' hstep
      exact ⟨evs ++ tr, c2, err_evs, star.star_step _ _ _ _ _ hstep hstar, herr⟩
    | SError => exact ⟨[], c, evs, star.star_refl c, hstep⟩

/-! ## Initial machine state at `execve` -/

variable (mi_init_pc : Nat)
variable (mi_phdrs : PhdrInfo)
variable (mi_init_sp : word)
variable (mi_init_brk : word)
variable (mi_mmap_base : word)

/- The 16 bytes of startup entropy AT_RANDOM points at, drawn afresh at
`execve` exactly like `mi_init_sp`, `mi_init_brk` and `mi_mmap_base`
(`get_random_bytes` in `create_elf_tables`, fs/binfmt_elf.c, Linux v6.18.46,
commit 1f99e9ab748f).  Unlike the three placements it has NO validity
predicate: every 128-bit value is a draw the kernel can make.  Declared here,
after the three placements and before the budget, so that `init_config` takes
its arguments in the Rocq order `segs pc ph sp brk0 mbase rnd lim inp`. -/
variable (mi_draw : EntryDraw)

/-! ### The entry stack image: the block, then the rest of its page

`StackLayout.build_stack_bytes` is what the kernel WRITES.  What it MAPS is
whole pages: the stack is a VMA and `setup_arg_pages` (fs/exec.c, Linux
v6.18.46, commit 1f99e9ab748f) page-aligns its top, so mapping exactly the
block left the rest of the page it ends in unmapped — a fault the model
produced and no kernel does (issue #668).  The bytes up there are the
entry's own `ed_slack` draw; see the Rocq twin for the argument. -/

def entry_block_top (sp : word) (bytes : List byte) : Int :=
  bv_unsigned sp + (bytes.length : Int)

def entry_page_top (sp : word) (bytes : List byte) : Int :=
  page_round_up_Z (entry_block_top sp bytes)

def entry_slack_len (sp : word) (bytes : List byte) : Nat :=
  (entry_page_top sp bytes - entry_block_top sp bytes).toNat

def entry_slack (sp : word) (bytes : List byte) (slack : word → byte) : List byte :=
  (List.range (entry_slack_len sp bytes)).map
    (fun k : Nat => slack (Z_to_bv 64 (entry_block_top sp bytes + (k : Int))))

def entry_stack_image (ph : PhdrInfo) (sp : word) (argv envp : List (List byte))
    (uid hwcap : word) (draw : EntryDraw) : List byte :=
  let bytes := build_stack_bytes ph sp argv envp uid hwcap draw
  bytes ++ entry_slack sp bytes draw.ed_slack

/-- The page boundary is at or above the block's top: rounding up never
moves an address down.  Everything below rests on this, so it is proved
here rather than assumed at each use. -/
theorem entry_page_top_ge (sp : word) (bytes : List byte) :
    entry_block_top sp bytes ≤ entry_page_top sp bytes := by
  unfold entry_page_top page_round_up_Z page_size
  omega

theorem length_entry_slack (sp : word) (bytes : List byte) (slack : word → byte) :
    (entry_slack sp bytes slack).length = entry_slack_len sp bytes := by
  unfold entry_slack
  rw [List.length_map, List.length_range]

/-- NO ADDRESS IN THE LAYOUT MOVES: the slack is a SUFFIX, so every byte
`build_stack_bytes` writes is still at the offset it wrote it at.  In
Rocq this is what keeps every concrete-layout proof — the argc word, the
argv and envp pointers, the auxv, the strings, the AT_RANDOM block —
reading exactly what it read before the page was mapped whole.
`Common/PropExec.lean`'s `read_argc` reaches it as Rocq's does: through
`read_at_offset_image` and `rdn_image_in_block` there, then
`stack_to_mem_image_in_block` below. -/
theorem entry_stack_image_block_prefix (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw) (i : Nat)
    (hi : i < (build_stack_bytes ph sp argv envp uid hwcap draw).length) :
    (entry_stack_image ph sp argv envp uid hwcap draw)[i]?
      = (build_stack_bytes ph sp argv envp uid hwcap draw)[i]? := by
  unfold entry_stack_image
  exact List.getElem?_append_left hi

/-- INSIDE THE BLOCK, the image answers exactly as the block does.  A
read-back — the argc word, the argv and envp pointers, the auxv slots, the
strings — is about an address below `entry_block_top`, so this one step
sees it past the page the model maps whole; Rocq's read-back lemmas each
take it. -/
theorem stack_to_mem_image_in_block (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw) (addr : word)
    (hlt : bv_unsigned addr
      < entry_block_top sp (build_stack_bytes ph sp argv envp uid hwcap draw)) :
    stack_to_mem sp (entry_stack_image ph sp argv envp uid hwcap draw) addr
      = stack_to_mem sp (build_stack_bytes ph sp argv envp uid hwcap draw) addr := by
  unfold entry_block_top at hlt
  unfold stack_to_mem
  by_cases hle : bv_unsigned sp ≤ bv_unsigned addr
  · have hoff : (bv_unsigned addr - bv_unsigned sp).toNat
        < (build_stack_bytes ph sp argv envp uid hwcap draw).length := by omega
    have him : ((build_stack_bytes ph sp argv envp uid hwcap draw).length : Int)
        ≤ ((entry_stack_image ph sp argv envp uid hwcap draw).length : Int) := by
      unfold entry_stack_image
      simp only [List.length_append]
      omega
    have h1 : bv_unsigned addr - bv_unsigned sp
        < ((entry_stack_image ph sp argv envp uid hwcap draw).length : Int) := by omega
    have h2 : bv_unsigned addr - bv_unsigned sp
        < ((build_stack_bytes ph sp argv envp uid hwcap draw).length : Int) := by omega
    simp only [hle, h1, h2, ↓reduceIte]
    exact entry_stack_image_block_prefix ph sp argv envp uid hwcap draw _ hoff
  · simp only [hle, ↓reduceIte]

/-- The image ends exactly at the page boundary above the block. -/
theorem entry_stack_image_top (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw) :
    bv_unsigned sp + ((entry_stack_image ph sp argv envp uid hwcap draw).length : Int)
      = entry_page_top sp (build_stack_bytes ph sp argv envp uid hwcap draw) := by
  have hge := entry_page_top_ge sp (build_stack_bytes ph sp argv envp uid hwcap draw)
  unfold entry_stack_image
  simp only [List.length_append, length_entry_slack]
  unfold entry_slack_len entry_page_top entry_block_top at *
  omega

/-- Sets PC (from the snapshot); SP (x2) is the quantified `mi_init_sp`;
populates stack memory from the argv/envp/auxv layout; the dynamic stack
region below SP is zero-mapped.  All other registers start at 0; the FP
state is zeroed; no LR/SC reservation is held.  `uid` is the run's
`in_uid`, the same field `init_model` copies into the credentials, so
AT_UID on the stack and `getuid`'s answer come from ONE source. -/
def init_machine_state (argv : List (List byte))
    (envp : List (List byte)) (uid hwcap : word) : machine_state :=
  let regs :=
    bvmap_set 2 mi_init_sp                 -- sp
      (bvmap_set 10 (Z_to_bv 64 0)         -- a0 — 0 on Linux entry; redundant
                                           -- (missing keys read as 0) but kept
                                           -- for the map shape, as in Rocq
         bvmap_empty)                      -- every other register reads as 0
  { ms_regs := regs, ms_fregs := bvmap_empty,
    ms_pc_val := Z_to_bv 64 (mi_init_pc : Int),
    ms_svc_pending := none,
    ms_resv := none, ms_fcsr := Z_to_bv 32 0,
    ms_mem :=
      let stk := stack_to_mem mi_init_sp
                   (entry_stack_image mi_phdrs mi_init_sp argv envp uid hwcap mi_draw)
      fun addr =>
        match stk addr with
        | some b => some b
        | none =>
          if (bv_unsigned mi_init_sp - stack_max_size ≤ bv_unsigned addr)
             && (bv_unsigned addr < bv_unsigned mi_init_sp)
          then some (Z_to_bv 8 0)
          else none,
    ms_rom := fun addr =>
      match memory_read mi_loaded_segments addr 1 with
      | some (b :: _) => some b
      | _ => none }

/- The run's backed anonymous-memory budget in BYTES (`State.vm_limit`):
`State.vm_backing_used` may never rise above it, so the out-of-memory point
of an unboundedly-allocating program is forced by a fixed budget rather
than a quantified draw (issue #131).  A parameter so harnesses can seed
small budgets; `Equivalence.strong_equiv` pins it per role to
`State.source_alloc_limit`/`State.target_alloc_limit`.  Not a step count
and not a syscall limit. -/
variable (mi_alloc_limit : Int)

/-- The initial configuration for one run of THIS image on the
caller-supplied inputs `inp`. -/
def init_config (inp : ProcInput) : config :=
  config.mkCfg (init_machine_state mi_loaded_segments mi_init_pc mi_phdrs mi_init_sp
                  mi_draw inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved mi_loaded_segments) mi_init_brk
                    mi_mmap_base mi_init_sp mi_alloc_limit inp)

end WithMemImage

/-! ## Running a binary: the three groups of arguments -/

/-- What `execve` chooses for THIS run: the initial stack pointer, the
program break and the mmap base — all placed non-deterministically — and the
`StackLayout.EntryDraw`, the two byte-level choices in the entry stack image
the model does not determine.  All four are quantified independently per
binary; only the first three have a window, which is why `valid_entry` below
says nothing about `en_draw`. -/
structure ExecEntry where
  mkEntry ::
  en_sp        : word
  en_brk       : word
  en_mmap_base : word
  en_draw      : EntryDraw

/-- Everything observable about one binary on one input.  Rocq writes this
as a `match` on the image and the entry so `cbn` reaches `init_config`;
Lean's structure projections reduce on their own, so the projections are
used directly and the two are definitionally the same. -/
def run (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : behavior :=
  let c0 := init_config img.img_segments img.img_init_pc img.img_phdrs
              en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp
  { bh_traces := obs_trace img.img_segments c0,
    bh_errors := reaches_error img.img_segments c0,
    bh_all_errors := all_traces_error img.img_segments c0,
    bh_unmodeled := reaches_unmodeled img.img_segments c0 }

/-! ## Spurious environment failures, per family: `SpuriousCfg` and `run_scfg`

WHAT IS PARAMETERISED.  Some arms answer an errno the model cannot DERIVE
from its state — `openat` of a file that exists may still fail with -ENOMEM
or -EACCES, `dup` with -EMFILE, `mmap` with -ENOMEM while budget remains,
`getrandom` with -EINTR.  Each draws from a per-syscall list with
`Syscall.errno_from` under an `alt` beside the answer the state does
determine, so that the failure stays LIVE: a target that deleted the
source's error handling would otherwise remain equivalent.  That reading
makes two things unprovable a task may want — an error-free statement about
a program whose out-of-memory path aborts although its allocations never
come near the budget (issue #570), and a `Classifier.decides` statement
about a classifier that reads its input file (issue #583) — so a task
chooses, per FAMILY of injected failure, between MAY FAIL (the reading
every statement above has) and FAILS ONLY IF FORCED (the errno is admitted
only where the model's state leaves no other answer).  The choice is a
parameter of a STATEMENT, not a field of the model and not a quantified
draw, so nothing under `Sys/` and nothing in `State` changes.

WHERE "FORCED" COMES FROM.  It is not written anywhere as a state test; it
is read off the spec by `spurious_refusal_cfg`, which removes a refusal
only where the spec admits, at the same input and model, an outcome that is
NOT one.  So, with its family off, a refusal is kept exactly where every
answer the spec admits there is a refusal: for instance `setsid`'s -EPERM
after a success, keyed on `State.m_setsid_succeeded`, and `mmap`'s -ENOMEM
at its argument gate (`setsid_eperm_forced_after_success` and
`mmap_gate_enomem_kept_under_forced_only` in `Checks/SpuriousCfg.lean`).  `Run.v` tabulates the places per family
instead, and the table is not carried here because at least two of its
rows leave places out.  Its fs row gives openat alone, but `unlinkat` with
AT_REMOVEDIR on "/" answers -EBUSY and nothing else
(`Checks/Cases/Fs/Namei.lean`'s `root_rmdir_is_ebusy`), and -EBUSY is on
`unlinkat_errnos`.  Its alloc row gives the budget test and placement,
but not the argument gates, such as the one
`mmap_gate_enomem_kept_under_forced_only` fires.  `brk` is the one arm
that refuses by VALUE, answering the old break, so its entry carries no
list and `brk_refusal_b` names the refusal.

EXACT AGAINST THE SPEC, NOT AGAINST LINUX.  By construction rather than by
mirroring each arm's branches: where every answer the spec admits at
`(i, m)` is a refusal, none of them is removed, since
`spurious_refusal_cfg`'s third conjunct asks for one that is not, and an
answer that is not a refusal is removed nowhere
(`spurious_refusal_not_refusal`).  The condition is the point: a
determined answer that IS on its arm's list is kept because no
non-refusal outcome stands beside it, not because it is off the list
(`Checks/SpuriousCfg.lean`'s `mmap_gate_enomem_kept_under_forced_only`).
`Run.v` concludes that a wrong or over-inclusive errno list can only LOSE
filtering, never remove an answer Linux is forced to give.  That holds
only on a premise the filter does not check: wherever the spec admits an
answer that is not a refusal, no supported implementation is forced to a
refusal at that state.  A refusal the spec admits beside an answer that is
not one stands for a condition the model does not track; where that
condition holds, Linux gives the refusal while the spec still admits what
stands beside it, and the premise fails there, as it does where the
supported implementations differ.  So a statement made under a
forced-only configuration also ASSUMES that none of its runs meets such a
condition in a family the configuration turns off.  Nothing in the
statement's text carries that assumption; choosing the configuration
makes it.  For an allocator that fails, the assumption is what the
configuration is for (issue #570); where the condition is a fact of the
launching environment, or a choice the supported implementations make
differently, it is easy to miss.  The places below are of that second
kind, and they are examples, not a census: `Fs.Namei.unlinkat_errnos`
names four more conditions of that kind, a read-only mount, the parent's
permission bits, an append-only or immutable entry and a mount point over
the entry, each forcing Linux to a refusal where the spec admits the
unlink beside it, and nothing enumerates the rest.

The descriptor allocators.  `Fs.File.lowest_fd` reads no limit, so an arm
that allocates through it and injects -EMFILE, as `dup` does, admits the
lowest free descriptor beside the -EMFILE even where `alloc_fd`'s
`fd >= end` test (fs/file.c:591-593, Linux v6.18.46), with `end` the soft
RLIMIT_NOFILE, forces Linux to -EMFILE; with the arm's family off, `sc_fd`
for `dup`, the filter removes the -EMFILE and leaves only the descriptor
(`Checks/Cases/Run.lean`'s `dup_emfile_at_the_soft_limit_is_filtered`).
bugs/fd-allocation-ignores-rlimit-nofile.md records the allocator's gap,
not this consequence of it.

`setsid` from a session or process-group leader.  `ksys_setsid`
(kernel/sys.c:1268-1301, Linux v6.18.46) answers -EPERM when the caller
already leads a session (:1278-1279) or its `pid_task(sid, PIDTYPE_PGID)`
test (:1284-1285) finds a task, as it does when the caller leads its own
process group, while `Kernel.Sys.setsid_spec` admits a session id beside
the -EPERM on a first call, since neither fact is in `State.ProcInput`;
with `sc_cred` off the filter removes the -EPERM
(`Checks/SpuriousCfg.lean`'s `setsid_eperm_spurious_before_success`).

`getcwd` in a removed working directory, or one whose path is `PATH_MAX`
bytes or longer.  `SYSCALL_DEFINE2(getcwd)` (fs/d_path.c:412-448, Linux
v6.18.46) answers -ENOENT when its `d_unlinked(pwd.dentry)` test
(:424-426) finds the working directory removed, and -ENAMETOOLONG when the
path it assembles overflows (:436-438), both before its size comparison
(:439-440); there it answers one of the two, or -ENOMEM if it cannot
allocate its page (:416-419), and not -ERANGE.  The model has no working
directory, and `Fs.DPath.getcwd_spec` admits -ERANGE beside those three
wherever it answers; with `sc_fs` off the filter removes the -ENOENT and
the -ENAMETOOLONG (`Checks/SpuriousCfg.lean`'s
`getcwd_enoent_enametoolong_spurious_under_forced_only`).

`brk`, in at least three places, in `Run.v` as here: `brk_refusal_b` is
written as `Run.v` writes it, and `Mmap.brk_spec`, `brk_r_ok` and
`brk_grow_ok` as `Mmap.v` writes them.  On a SHRINK over nothing mapped,
`SYSCALL_DEFINE1(brk)` (mm/mmap.c, Linux v6.18.46) is forced to the old
break by `if (!brkvma || brkvma->vm_start >= oldbrk) goto out;`, while in
Linux v4.17, v5.15 and v6.0 the same syscall answers the request, because
its unmap step, `do_munmap` and later `__do_munmap` in the same file,
returns 0 over a range that meets no VMA; so does QEMU 11.1.1's user-mode
`do_brk` (linux-user/syscall.c), which ignores what its unmap returns.
`Mmap.brk_r_ok` admits both answers, as it must, and `brk_refusal_b` counts
the old break as a refusal, so with `sc_alloc = false` the answer v6.18.46
gives is removed (`Checks/Cases/Run.lean`'s
`brk_shrink_over_nothing_mapped_is_filtered`).  The repair belongs in
`brk_refusal_b`, in `Run.v` first: narrowing `brk_r_ok` instead would take
the older kernels' and QEMU's answer out of `run` too.  The other two are
GROWs Linux refuses and `brk_r_ok` admits: into the stack guard gap
(bugs/brk-grow-ignores-stack-guard-gap.md), and onto the vvar/vdso pair,
which the ledger does not hold (bugs/grants-into-the-stack-band.md).

The filtered run is a subset of `run` (`sstep_cfg_sub` and the `_sub`
lemmas below) and agrees with it at `may_fail_cfg`, step for step
(`sstep_cfg_may_fail`) and observation by observation
(`run_scfg_may_fail`): nothing is spurious there
(`spurious_refusal_may_fail`), so `may_fail_cfg` keeps the forced answer
at these places and stays sound.

KNOWN GAP.  `Checks.ExecutableSpecs` decides membership of ONE outcome and
`Checks.Progress` exhibits ONE admissible outcome per input; neither
answers the question the filter asks, whether a NON-REFUSAL outcome exists
at `(i, m)`.  For `mmap` and `mremap` that is a placement question nothing
in the trusted tree computes, so the conformance harness certifies the
may-fail reading only; `refusal_decided` names the question and
`sstep_cfg_progress` shows the filtered run never gets stuck where it is
answered.  Answering it in the logic is free here: `Classical.em` proves
`refusal_decided` at every argument (`Checks/Cases/Run.lean`'s
`refusal_decided_classical`), and it stays a premise for parity with
`Run.v`, whose tree uses no classical axiom.  What stays open in both
trees is COMPUTING the answer.  The argument is ported from the Rocq
section's header (`Run.v`, "Spurious environment failures, per family"),
which also carries the per-family table this section does not. -/

/-- The six families of injected environment failure. -/
inductive SpuriousFamily : Type
  | FamAlloc | FamFs | FamFd | FamNet | FamCred | FamIntr
  deriving DecidableEq

export SpuriousFamily (FamAlloc FamFs FamFd FamNet FamCred FamIntr)

/-- One boolean per family: `true` = "always allowed to fail" (the reading
every statement above this section has), `false` = "fails only if
forced".  A structure rather than a function so a checker can spell a
configuration as a literal, as in Rocq. -/
structure SpuriousCfg where
  mkSpuriousCfg ::
  sc_alloc : Bool
  sc_fs    : Bool
  sc_fd    : Bool
  sc_net   : Bool
  sc_cred  : Bool
  sc_intr  : Bool

def may_fail_cfg : SpuriousCfg := SpuriousCfg.mkSpuriousCfg true true true true true true
def forced_only_cfg : SpuriousCfg := SpuriousCfg.mkSpuriousCfg false false false false false false

/-- Issue #570's one-switch form: the allocation family alone, every other
family left as it always was. -/
def alloc_only_cfg (alloc_may_fail : Bool) : SpuriousCfg :=
  SpuriousCfg.mkSpuriousCfg alloc_may_fail true true true true true

def family_may_fail (cfg : SpuriousCfg) (f : SpuriousFamily) : Bool :=
  match f with
  | FamAlloc => cfg.sc_alloc
  | FamFs    => cfg.sc_fs
  | FamFd    => cfg.sc_fd
  | FamNet   => cfg.sc_net
  | FamCred  => cfg.sc_cred
  | FamIntr  => cfg.sc_intr

/-- `cfg1` admits no family `cfg2` does not: the pointwise order on the six
booleans.  `forced_only_cfg` is its least element and `may_fail_cfg` its
greatest. -/
def cfg_le (cfg1 cfg2 : SpuriousCfg) : Prop :=
  ∀ f, family_may_fail cfg1 f = true → family_may_fail cfg2 f = true

theorem cfg_le_refl (cfg : SpuriousCfg) : cfg_le cfg cfg := fun _ h => h

theorem forced_only_cfg_least (cfg : SpuriousCfg) : cfg_le forced_only_cfg cfg := by
  intro f h
  cases f <;> exact absurd h Bool.false_ne_true

theorem may_fail_cfg_greatest (cfg : SpuriousCfg) : cfg_le cfg may_fail_cfg := by
  intro f _
  cases f <;> rfl

/-- One injecting arm: the syscall number, its family, and the errnos its
`Syscall.errno_from` draws from — the spec's own list, named rather than
copied. -/
structure InjectedArm where
  mkInjectedArm ::
  ia_no     : Int
  ia_family : SpuriousFamily
  ia_errnos : List Int

/-- The arms of the syscall table that inject, as `Run.v` lists them,
SORTED BY SYSCALL NUMBER like that table and for the same reason (two
changes that add two arms land at different lines).  `brk` refuses by
value and carries no list; see `brk_refusal_b`.  `nanosleep`'s -EINTR and
`setsid`'s -EPERM are injected by a bare `alt` rather than through a named
list, so their lists are written here.  `Run.v`'s docstring calls the
table every arm that injects, but `getdents64` (61) and `faccessat2` (439)
draw from `getdents64_errnos` and `faccessat_errnos` with
`Syscall.errno_from` and have no entry, in `Run.v` as here: none of their
answers is then a refusal, so the filter removes none of them
(`spurious_refusal_not_refusal`), and `Checks/Cases/Run.lean`'s
`injected_table_omits_getdents64_and_faccessat2` fails when an entry
lands.  (Rocq: `Run.injected_table`, entry for entry.) -/
def injected_table : List InjectedArm :=
  [ InjectedArm.mkInjectedArm  17 FamFs    getcwd_errnos,
    InjectedArm.mkInjectedArm  23 FamFd    dup_errnos,
    InjectedArm.mkInjectedArm  35 FamFs    unlinkat_errnos,
    InjectedArm.mkInjectedArm  48 FamFs    faccessat_errnos,
    InjectedArm.mkInjectedArm  56 FamFs    openat_errnos,
    InjectedArm.mkInjectedArm  59 FamFd    pipe2_errnos,
    InjectedArm.mkInjectedArm 101 FamIntr  [EINTR],
    InjectedArm.mkInjectedArm 144 FamCred  (setid_errnos true),
    InjectedArm.mkInjectedArm 146 FamCred  (setid_errnos true),
    InjectedArm.mkInjectedArm 147 FamCred  (setid_errnos true),
    InjectedArm.mkInjectedArm 149 FamCred  (setid_errnos true),
    InjectedArm.mkInjectedArm 157 FamCred  [EPERM],
    InjectedArm.mkInjectedArm 198 FamFd    socket_errnos,
    InjectedArm.mkInjectedArm 199 FamFd    (socketpair_reserve_errnos ++ socketpair_create_errnos),
    InjectedArm.mkInjectedArm 200 FamNet   bind_errnos,
    InjectedArm.mkInjectedArm 201 FamNet   listen_errnos,
    InjectedArm.mkInjectedArm 202 FamFd    accept_errnos,
    InjectedArm.mkInjectedArm 214 FamAlloc [],
    InjectedArm.mkInjectedArm 216 FamAlloc mremap_errnos,
    InjectedArm.mkInjectedArm 220 FamFd    clone_errnos,
    InjectedArm.mkInjectedArm 222 FamAlloc mmap_errnos,
    InjectedArm.mkInjectedArm 226 FamAlloc mprotect_errnos,
    InjectedArm.mkInjectedArm 242 FamFd    accept_errnos,
    InjectedArm.mkInjectedArm 278 FamIntr  getrandom_errnos,
    InjectedArm.mkInjectedArm 435 FamFd    clone_errnos ]

def lookup_injected (t : List InjectedArm) (n : Int) : Option InjectedArm :=
  match t with
  | [] => none
  | a :: r => if a.ia_no = n then some a else lookup_injected r n

/-- The injecting arm for a syscall number, keyed exactly as
`Sys.Dispatch.dispatch` keys the spec table. -/
def injected_arm (no : Int) : Option InjectedArm :=
  lookup_injected injected_table no

/-- `r` is one of the errno returns in `es`. -/
def ret_in_errnos (es : List Int) (r : word) : Bool :=
  es.any (fun e => bv_eqb r (errno_ret e))

/-- `brk req` answered `ret` from the pre-step model `m`: a refusal iff
`req` is a real request (neither the query nor an address below
`Mmap.min_brk`, both of which the state answers with the old break), asks
to MOVE the break, and the answer is the old break unmoved.  On the three
requests excluded, `Mmap.brk_r_ok` admits the old break alone, so counting
them as refusals would change nothing the filter does; excluding them
keeps a refusal a refused MOVE.  On a move, a grow or a shrink, the old
break counts as a refusal whatever the state, which is exact only while no
supported implementation is forced to the old break where `brk_r_ok`
admits the move; the section header names the places known to break
that. -/
def brk_refusal_b (m : Model) (req ret : word) : Bool :=
  let h := m_vmmaps m
  let b := h.vm_brk
  !(w_is0 req)
  && !(decide (bv_unsigned req < bv_unsigned (min_brk h)))
  && !(bv_eqb req b)
  && bv_eqb ret b

/-- Is the answer `ret` to the syscall `i` at model `m` one of its injected
refusals?  For every arm but `brk`, one of the listed errnos; for `brk`,
the old break on a request to move it.  A syscall with no injecting arm has
no refusals. -/
def refusal_b (i : SyscallInput) (m : Model) (ret : word) : Bool :=
  let no := bv_unsigned i.in_sysno
  if no = 214 then brk_refusal_b m (in_arg i 0) ret
  else match injected_arm no with
       | some a => ret_in_errnos a.ia_errnos ret
       | none => false

/-! ## The budget mark's dispatcher

Is the pending syscall `i` at model `m` a grant the BUDGET refuses?  Every
allocation arm answers through the mark its own file defines beside its
spec (`Mmap.brk_budget_refused_b`, `Mremap.mremap_budget_refused_b`,
`Mmap.mmap_budget_refused_b`, `Mprotect.mprotect_budget_refused_b`),
on the arguments `Sys.SyscallTable.spec_table` hands the arm; every other
number is `false`.  The mark asks whether the REQUEST is one the budget
declines, whatever answer is then drawn; the argument for the shape, and
for why the `false` is the dangerous answer — an allocation arm this
dispatcher does not know is a silent false negative of the budget premise
— is on the Rocq `Run.alloc_budget_refused_b`.

TWO LEMMAS TIE THE LIST DOWN, as in Rocq.  `alloc_family_dispatched`
below proves that every number `injected_table` registers under `FamAlloc`
is in `alloc_mark_sysnos`, so a fifth `FamAlloc` arm fails to build until
the list carries its number, and `alloc_budget_refused_b_outside` that the
dispatcher answers `false` everywhere off that list.  Neither reads the
dispatcher's arms for a number ON the list: one the list gains with no arm
below falls to the `false` default, and this file still builds, since
`alloc_mark_sysnos_dispatched` states the four arms written out.
`Checks/Cases/Run.lean`'s `each_listed_number_reaches_a_refusing_mark`
then fails to build: it asks, for each number on the list, for an input
the dispatcher answers `true` on, which the default does not supply.  An arm
that consults the budget without registering as injecting at all is
`tools/check_budget_marks.py`'s to catch, in the generated-docs job: its
ARMS rule has every `_spec` that consults the budget define a mark, and
its DISPATCH rule fails while a mark it finds goes unnamed here; neither
rule reads the list.  `Checks/Cases/Run.lean`'s
`alloc_mark_sysnos_are_modeled` holds every number here to be a modeled
arm of the Lean syscall table, the other half of the list's honesty on
this side: the mark of a declined number would answer for an arm that
does not exist.  Porting an allocation arm therefore adds its number here,
its mark's arm below and a refused request for it to that pin — not in
the port PR, which may not edit this frozen file, but in a companion
`lean: base:` change (the mremap arm came with #810, its dispatch as
5f949aa7 straight onto the day branch).  The dispatch cannot land first:
this file would name a mark nothing defines, which neither the build nor
that tool's DISPATCH rule accepts.  So that job is red on the day branch
between the two, and the companion follows the port at once. -/
def alloc_mark_sysnos : List Int := [214, 216, 222, 226]

def alloc_budget_refused_b (i : SyscallInput) (m : Model) : Bool :=
  let no := bv_unsigned i.in_sysno
  if no = 214 then
    brk_budget_refused_b m (in_arg i 0)
  else if no = 216 then
    mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m
  else if no = 222 then
    mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
      (in_arg i 4) (in_arg i 5) m
  else if no = 226 then
    mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) m
  else false

theorem lookup_injected_in (t : List InjectedArm) (n : Int) (a : InjectedArm) :
    lookup_injected t n = some a → a ∈ t ∧ a.ia_no = n := by
  induction t with
  | nil => intro h; exact nomatch h
  | cons x t ih =>
    intro h
    by_cases e : x.ia_no = n
    · simp only [lookup_injected, e, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨List.mem_cons.2 (Or.inl rfl), e⟩
    · simp only [lookup_injected, e, ↓reduceIte] at h
      obtain ⟨hin, hno⟩ := ih h
      exact ⟨List.mem_cons.2 (Or.inr hin), hno⟩

/-- Every `FamAlloc` arm is on the list.  Rocq proves it by case analysis
over the table's entries; here the same case analysis is `decide` over the
table, so an arm added to it under `FamAlloc` still breaks this proof until
`alloc_mark_sysnos` carries its number.  The dispatcher is not read here;
this section's header says what holds its arms to the list. -/
theorem alloc_family_dispatched (no : Int) (a : InjectedArm) :
    injected_arm no = some a → a.ia_family = FamAlloc → no ∈ alloc_mark_sysnos := by
  intro h hf
  obtain ⟨hin, rfl⟩ := lookup_injected_in injected_table no a h
  have hall : ∀ x ∈ injected_table, x.ia_family = FamAlloc → x.ia_no ∈ alloc_mark_sysnos := by
    decide
  exact hall a hin hf

/-- Every number ON the list today is dispatched to its arm's mark, one
conjunct per number, written out.  A number the list gains does not grow
the statement, so one added without a dispatcher arm does not go red here;
this section's header says what catches it.  (Rocq:
`Run.alloc_mark_sysnos_dispatched`, with four conjuncts.) -/
theorem alloc_mark_sysnos_dispatched (i : SyscallInput) (m : Model) :
    (bv_unsigned i.in_sysno = 214 →
      alloc_budget_refused_b i m = brk_budget_refused_b m (in_arg i 0))
    ∧ (bv_unsigned i.in_sysno = 216 →
      alloc_budget_refused_b i m
        = mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m)
    ∧ (bv_unsigned i.in_sysno = 222 →
      alloc_budget_refused_b i m
        = mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
            (in_arg i 4) (in_arg i 5) m)
    ∧ (bv_unsigned i.in_sysno = 226 →
      alloc_budget_refused_b i m
        = mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) m) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp +decide only [alloc_budget_refused_b, h, ↓reduceIte]
  · simp +decide only [alloc_budget_refused_b, h, ↓reduceIte]
  · simp +decide only [alloc_budget_refused_b, h, ↓reduceIte]
  · simp +decide only [alloc_budget_refused_b, h, ↓reduceIte]

/-- …and the dispatcher answers `false` everywhere off the list, which ties
`alloc_mark_sysnos` to the numbers it tests.  (Rocq:
`Run.alloc_budget_refused_b_outside`.) -/
theorem alloc_budget_refused_b_outside (i : SyscallInput) (m : Model) :
    bv_unsigned i.in_sysno ∉ alloc_mark_sysnos → alloc_budget_refused_b i m = false := by
  intro hout
  have h0 : bv_unsigned i.in_sysno ≠ 214 := fun e => hout (by rw [e]; decide)
  have h3 : bv_unsigned i.in_sysno ≠ 216 := fun e => hout (by rw [e]; decide)
  have h1 : bv_unsigned i.in_sysno ≠ 222 := fun e => hout (by rw [e]; decide)
  have h2 : bv_unsigned i.in_sysno ≠ 226 := fun e => hout (by rw [e]; decide)
  simp only [alloc_budget_refused_b, h0, h3, h1, h2, ↓reduceIte]

/-- The syscall `i` belongs to a family `cfg` reads as forced-only. -/
def injected_family_off (cfg : SpuriousCfg) (i : SyscallInput) : Bool :=
  match injected_arm (bv_unsigned i.in_sysno) with
  | some a => !(family_may_fail cfg a.ia_family)
  | none => false

/-- The one decision a forced-only family adds to a syscall step: is this
outcome a refusal the state did not force?  Three conjuncts — the family is
off, the answer is a refusal, and the spec admits a non-refusal answer at the
same input and model.  The third is what makes the filter exact against
the spec; this section's header says where that falls short of Linux. -/
def spurious_refusal_cfg (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) : Prop :=
  injected_family_off cfg i = true
  ∧ refusal_b i m eff.eff_ret = true
  ∧ (∃ eff' m' evs',
        syscall_spec i m (Ok eff' m' evs') ∧ refusal_b i m eff'.eff_ret = false)

/-- The question the KNOWN GAP is about, stated once: at `(i, m)`, if the
syscall's family is off in `cfg`, then either a non-refusal outcome exists or
every admissible outcome is a refusal.  Vacuous for a family that may fail
and for a syscall that injects nothing; no procedure in this tree decides
it for the rest — for `mmap` it is the placement question.  `Run.v`'s
`sstep_cfg_progress` takes it as a premise because that tree has no
classical axiom to prove it with in general.  Here `Classical.em` proves
it at every argument (`Checks/Cases/Run.lean`'s
`refusal_decided_classical`), and the premise is kept so that the
statement stays Rocq's. -/
def refusal_decided (cfg : SpuriousCfg) (i : SyscallInput) (m : Model) : Prop :=
  injected_family_off cfg i = true →
  (∃ eff' m' evs',
     syscall_spec i m (Ok eff' m' evs') ∧ refusal_b i m eff'.eff_ret = false)
  ∨ (∀ eff' m' evs',
        syscall_spec i m (Ok eff' m' evs') → refusal_b i m eff'.eff_ret = true)

theorem injected_family_off_may_fail (i : SyscallInput) :
    injected_family_off may_fail_cfg i = false := by
  unfold injected_family_off
  cases injected_arm (bv_unsigned i.in_sysno) with
  | none => rfl
  | some a =>
    rcases a with ⟨no, f, es⟩
    cases f <;> rfl

/-- Under the may-fail reading nothing is spurious: that is what makes
`may_fail_cfg` the reading every existing statement has. -/
theorem spurious_refusal_may_fail (i : SyscallInput) (m : Model) (eff : SyscallEffect) :
    ¬ spurious_refusal_cfg may_fail_cfg i m eff := by
  rintro ⟨hoff, _, _⟩
  rw [injected_family_off_may_fail] at hoff
  exact Bool.false_ne_true hoff

/-- A non-refusal outcome is never spurious, whatever the configuration. -/
theorem spurious_refusal_not_refusal (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) :
    refusal_b i m eff.eff_ret = false → ¬ spurious_refusal_cfg cfg i m eff := by
  rintro hnr ⟨_, hr, _⟩
  rw [hnr] at hr
  exact Bool.false_ne_true hr

/-- …and neither is any outcome of a family that may fail. -/
theorem spurious_refusal_family_on (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) :
    injected_family_off cfg i = false → ¬ spurious_refusal_cfg cfg i m eff := by
  rintro hon ⟨hoff, _, _⟩
  rw [hon] at hoff
  exact Bool.false_ne_true hoff

/-- Turning families off only makes more outcomes spurious. -/
theorem spurious_refusal_mono (cfg1 cfg2 : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) :
    cfg_le cfg1 cfg2 → spurious_refusal_cfg cfg2 i m eff → spurious_refusal_cfg cfg1 i m eff := by
  rintro hle ⟨hoff, hr, hex⟩
  refine ⟨?_, hr, hex⟩
  unfold injected_family_off at hoff ⊢
  cases h : injected_arm (bv_unsigned i.in_sysno) with
  | none =>
    rw [h] at hoff
    exact hoff
  | some a =>
    rw [h] at hoff
    have hoff' : (!(family_may_fail cfg2 a.ia_family)) = true := hoff
    show (!(family_may_fail cfg1 a.ia_family)) = true
    cases h1 : family_may_fail cfg1 a.ia_family with
    | false => rfl
    | true =>
      rw [hle a.ia_family h1] at hoff'
      exact (Bool.false_ne_true hoff').elim

section StepCfg

variable (segs : List Segment)

/-- `sstep` under a configuration: every constructor is `sstep`'s, and the
two that consume a syscall outcome additionally require the outcome not to
be a spurious refusal.  The exit constructor needs no such premise — an exit
is never a refusal — and neither does the fail-closed `Unmodeled` arm, which
is not an outcome at all.  Rocq's `Section StepCfg` variable `segs` is the
explicit first argument here, as `sstep` takes it. -/
inductive sstep_cfg (cfg : SpuriousCfg) : config → List event → step_to → Prop
  | sstep_cfg_instr : ∀ ms model ms' model',
      m_halted model = none →
      ms.ms_svc_pending = none →
      mi_account_step segs ms model = MachineOk (ms', model') →
      sstep_cfg cfg (config.mkCfg ms model) [] (SNext (config.mkCfg ms' model'))
  | sstep_cfg_instr_fault : ∀ ms model,
      m_halted model = none →
      ms.ms_svc_pending = none →
      mi_account_step segs ms model = MachineFault →
      sstep_cfg cfg (config.mkCfg ms model) [] SError
  | sstep_cfg_instr_unmodeled : ∀ ms model,
      m_halted model = none →
      ms.ms_svc_pending = none →
      mi_account_step segs ms model = MachineUnmodeled →
      sstep_cfg cfg (config.mkCfg ms model) [] SError
  | sstep_cfg_syscall : ∀ ms model x8 eff model' model'' evs,
      m_halted model = none →
      ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
      ¬ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff →
      m_halted model' = none →
      materialize_model_accesses model' (syscall_effect_accesses eff) = some model'' →
      sstep_cfg cfg (config.mkCfg ms model) evs
            (SNext (config.mkCfg (advance_past_svc (apply_effect ms eff)) model''))
  | sstep_cfg_syscall_materialization_fault : ∀ ms model x8 eff model' evs,
      m_halted model = none →
      ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
      ¬ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff →
      m_halted model' = none →
      materialize_model_accesses model' (syscall_effect_accesses eff) = none →
      sstep_cfg cfg (config.mkCfg ms model) [] SError
  | sstep_cfg_exit : ∀ ms model x8 eff model' evs code,
      m_halted model = none →
      ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
      m_halted model' = some code →
      m_killed model' = none →
      sstep_cfg cfg (config.mkCfg ms model) (evs ++ [ExitEv code (m_fs model')])
            (SNext (config.mkCfg ms model'))
  | sstep_cfg_killed : ∀ ms model x8 eff model' evs sig,
      m_halted model = none →
      ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
      m_killed model' = some sig →
      sstep_cfg cfg (config.mkCfg ms model) (evs ++ [KillEv sig (m_fs model')])
            (SNext (config.mkCfg ms model'))
  | sstep_cfg_syscall_unmodeled : ∀ ms model x8,
      m_halted model = none →
      ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model Unmodeled →
      sstep_cfg cfg (config.mkCfg ms model) [] SError

/-- SUBSET: every filtered step is a step. -/
theorem sstep_cfg_sub (cfg : SpuriousCfg) (c : config) (evs : List event) (r : step_to) :
    sstep_cfg segs cfg c evs r → sstep segs c evs r := by
  intro h
  cases h with
  | sstep_cfg_instr ms model ms' model' hh hsvc hstep =>
    exact sstep.sstep_instr ms model ms' model' hh hsvc hstep
  | sstep_cfg_instr_fault ms model hh hsvc hstep =>
    exact sstep.sstep_instr_fault ms model hh hsvc hstep
  | sstep_cfg_instr_unmodeled ms model hh hsvc hstep =>
    exact sstep.sstep_instr_unmodeled ms model hh hsvc hstep
  | sstep_cfg_syscall ms model x8 eff model' model'' evs hh hsvc hspec _ hh' hmat =>
    exact sstep.sstep_syscall ms model x8 eff model' model'' evs hh hsvc hspec hh' hmat
  | sstep_cfg_syscall_materialization_fault ms model x8 eff model' evs hh hsvc hspec _ hh'
      hmat =>
    exact sstep.sstep_syscall_materialization_fault ms model x8 eff model' evs hh hsvc hspec
      hh' hmat
  | sstep_cfg_exit ms model x8 eff model' evs code hh hsvc hspec hh' hk =>
    exact sstep.sstep_exit ms model x8 eff model' evs code hh hsvc hspec hh' hk
  | sstep_cfg_killed ms model x8 eff model' evs sig hh hsvc hspec hk =>
    exact sstep.sstep_killed ms model x8 eff model' evs sig hh hsvc hspec hk
  | sstep_cfg_syscall_unmodeled ms model x8 hh hsvc hspec =>
    exact sstep.sstep_syscall_unmodeled ms model x8 hh hsvc hspec

/-- MEANING: at `may_fail_cfg` the two relations coincide. -/
theorem sstep_cfg_may_fail (c : config) (evs : List event) (r : step_to) :
    sstep segs c evs r ↔ sstep_cfg segs may_fail_cfg c evs r := by
  constructor
  · intro h
    cases h with
    | sstep_instr ms model ms' model' hh hsvc hstep =>
      exact sstep_cfg.sstep_cfg_instr ms model ms' model' hh hsvc hstep
    | sstep_instr_fault ms model hh hsvc hstep =>
      exact sstep_cfg.sstep_cfg_instr_fault ms model hh hsvc hstep
    | sstep_instr_unmodeled ms model hh hsvc hstep =>
      exact sstep_cfg.sstep_cfg_instr_unmodeled ms model hh hsvc hstep
    | sstep_syscall ms model x8 eff model' model'' evs hh hsvc hspec hh' hmat =>
      exact sstep_cfg.sstep_cfg_syscall ms model x8 eff model' model'' evs hh hsvc hspec
        (spurious_refusal_may_fail _ _ _) hh' hmat
    | sstep_syscall_materialization_fault ms model x8 eff model' evs hh hsvc hspec hh' hmat =>
      exact sstep_cfg.sstep_cfg_syscall_materialization_fault ms model x8 eff model' evs hh
        hsvc hspec (spurious_refusal_may_fail _ _ _) hh' hmat
    | sstep_exit ms model x8 eff model' evs code hh hsvc hspec hh' hk =>
      exact sstep_cfg.sstep_cfg_exit ms model x8 eff model' evs code hh hsvc hspec hh' hk
    | sstep_killed ms model x8 eff model' evs sig hh hsvc hspec hk =>
      exact sstep_cfg.sstep_cfg_killed ms model x8 eff model' evs sig hh hsvc hspec hk
    | sstep_syscall_unmodeled ms model x8 hh hsvc hspec =>
      exact sstep_cfg.sstep_cfg_syscall_unmodeled ms model x8 hh hsvc hspec
  · exact sstep_cfg_sub segs may_fail_cfg c evs r

/-- MONOTONE: a configuration that admits more families admits more steps. -/
theorem sstep_cfg_mono (cfg1 cfg2 : SpuriousCfg) (c : config) (evs : List event) (r : step_to) :
    cfg_le cfg1 cfg2 → sstep_cfg segs cfg1 c evs r → sstep_cfg segs cfg2 c evs r := by
  intro hle h
  cases h with
  | sstep_cfg_instr ms model ms' model' hh hsvc hstep =>
    exact sstep_cfg.sstep_cfg_instr ms model ms' model' hh hsvc hstep
  | sstep_cfg_instr_fault ms model hh hsvc hstep =>
    exact sstep_cfg.sstep_cfg_instr_fault ms model hh hsvc hstep
  | sstep_cfg_instr_unmodeled ms model hh hsvc hstep =>
    exact sstep_cfg.sstep_cfg_instr_unmodeled ms model hh hsvc hstep
  | sstep_cfg_syscall ms model x8 eff model' model'' evs hh hsvc hspec hns hh' hmat =>
    exact sstep_cfg.sstep_cfg_syscall ms model x8 eff model' model'' evs hh hsvc hspec
      (fun hs => hns (spurious_refusal_mono cfg1 cfg2 _ _ _ hle hs)) hh' hmat
  | sstep_cfg_syscall_materialization_fault ms model x8 eff model' evs hh hsvc hspec hns hh'
      hmat =>
    exact sstep_cfg.sstep_cfg_syscall_materialization_fault ms model x8 eff model' evs hh
      hsvc hspec (fun hs => hns (spurious_refusal_mono cfg1 cfg2 _ _ _ hle hs)) hh' hmat
  | sstep_cfg_exit ms model x8 eff model' evs code hh hsvc hspec hh' hk =>
    exact sstep_cfg.sstep_cfg_exit ms model x8 eff model' evs code hh hsvc hspec hh' hk
  | sstep_cfg_killed ms model x8 eff model' evs sig hh hsvc hspec hk =>
    exact sstep_cfg.sstep_cfg_killed ms model x8 eff model' evs sig hh hsvc hspec hk
  | sstep_cfg_syscall_unmodeled ms model x8 hh hsvc hspec =>
    exact sstep_cfg.sstep_cfg_syscall_unmodeled ms model x8 hh hsvc hspec

/-- PROGRESS, where the filter's question is answered: a configuration with
a step has a filtered step.  The one case with content is a syscall outcome
that the filter removes; then, by the third conjunct of
`spurious_refusal_cfg`, a non-refusal outcome exists at the same input and
model, and that outcome — never spurious — is a step of one of the three
syscall shapes.  Deciding WHICH case one is in is the premise; see
`refusal_decided`. -/
theorem sstep_cfg_progress (cfg : SpuriousCfg) (ms : machine_state) (model : Model)
    (evs : List event) (st : step_to) :
    (∀ x8, ms.ms_svc_pending = some x8 → refusal_decided cfg (sys_input segs ms x8) model) →
    sstep segs (config.mkCfg ms model) evs st →
    ∃ evs' st', sstep_cfg segs cfg (config.mkCfg ms model) evs' st' := by
  intro hdec h
  -- A non-refusal outcome steps, whichever of the three syscall shapes it takes.
  have hnr_steps : ∀ x8 eff' m' evs', m_halted model = none → ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model (Ok eff' m' evs') →
      refusal_b (sys_input segs ms x8) model eff'.eff_ret = false →
      ∃ evs'' st', sstep_cfg segs cfg (config.mkCfg ms model) evs'' st' := by
    intro x8 eff' m' evs' hh hsvc hspec' hnr
    have hns := spurious_refusal_not_refusal cfg _ _ _ hnr
    cases hh' : m_halted m' with
    | some code =>
      cases hk' : m_killed m' with
      | some sig =>
        exact ⟨_, _, sstep_cfg.sstep_cfg_killed ms model x8 eff' m' evs' sig hh hsvc hspec' hk'⟩
      | none =>
        exact ⟨_, _, sstep_cfg.sstep_cfg_exit ms model x8 eff' m' evs' code hh hsvc hspec' hh'
          hk'⟩
    | none =>
      cases hmat : materialize_model_accesses m' (syscall_effect_accesses eff') with
      | some m'' =>
        exact ⟨_, _, sstep_cfg.sstep_cfg_syscall ms model x8 eff' m' m'' evs' hh hsvc hspec' hns
          hh' hmat⟩
      | none =>
        exact ⟨_, _, sstep_cfg.sstep_cfg_syscall_materialization_fault ms model x8 eff' m' evs'
          hh hsvc hspec' hns hh' hmat⟩
  cases h with
  | sstep_instr ms model ms' model' hh hsvc hstep =>
    exact ⟨_, _, sstep_cfg.sstep_cfg_instr ms model ms' model' hh hsvc hstep⟩
  | sstep_instr_fault ms model hh hsvc hstep =>
    exact ⟨_, _, sstep_cfg.sstep_cfg_instr_fault ms model hh hsvc hstep⟩
  | sstep_instr_unmodeled ms model hh hsvc hstep =>
    exact ⟨_, _, sstep_cfg.sstep_cfg_instr_unmodeled ms model hh hsvc hstep⟩
  | sstep_syscall ms model x8 eff model' model'' evs hh hsvc hspec hh' hmat =>
    -- an outcome that materializes: off-family refusals need the split
    cases hoff : injected_family_off cfg (sys_input segs ms x8) with
    | false =>
      exact ⟨_, _, sstep_cfg.sstep_cfg_syscall ms model x8 eff model' model'' evs hh hsvc hspec
        (spurious_refusal_family_on cfg _ _ _ hoff) hh' hmat⟩
    | true =>
      rcases hdec x8 hsvc hoff with ⟨eff', m', evs', hspec', hnr⟩ | hall
      · exact hnr_steps x8 eff' m' evs' hh hsvc hspec' hnr
      · -- every outcome is a refusal: none is spurious, so `eff` steps
        refine ⟨_, _, sstep_cfg.sstep_cfg_syscall ms model x8 eff model' model'' evs hh hsvc
          hspec ?_ hh' hmat⟩
        rintro ⟨_, _, eff'', m'', evs'', hspec'', hnr⟩
        rw [hall eff'' m'' evs'' hspec''] at hnr
        exact Bool.false_ne_true hnr.symm
  | sstep_syscall_materialization_fault ms model x8 eff model' evs hh hsvc hspec hh' hmat =>
    -- an outcome whose materialization faults: the same split
    cases hoff : injected_family_off cfg (sys_input segs ms x8) with
    | false =>
      exact ⟨_, _, sstep_cfg.sstep_cfg_syscall_materialization_fault ms model x8 eff model' evs
        hh hsvc hspec (spurious_refusal_family_on cfg _ _ _ hoff) hh' hmat⟩
    | true =>
      rcases hdec x8 hsvc hoff with ⟨eff', m', evs', hspec', hnr⟩ | hall
      · exact hnr_steps x8 eff' m' evs' hh hsvc hspec' hnr
      · refine ⟨_, _, sstep_cfg.sstep_cfg_syscall_materialization_fault ms model x8 eff model'
          evs hh hsvc hspec ?_ hh' hmat⟩
        rintro ⟨_, _, eff'', m'', evs'', hspec'', hnr⟩
        rw [hall eff'' m'' evs'' hspec''] at hnr
        exact Bool.false_ne_true hnr.symm
  | sstep_exit ms model x8 eff model' evs code hh hsvc hspec hh' hk =>
    exact ⟨_, _, sstep_cfg.sstep_cfg_exit ms model x8 eff model' evs code hh hsvc hspec hh' hk⟩
  | sstep_killed ms model x8 eff model' evs sig hh hsvc hspec hk =>
    exact ⟨_, _, sstep_cfg.sstep_cfg_killed ms model x8 eff model' evs sig hh hsvc hspec hk⟩
  | sstep_syscall_unmodeled ms model x8 hh hsvc hspec =>
    exact ⟨_, _, sstep_cfg.sstep_cfg_syscall_unmodeled ms model x8 hh hsvc hspec⟩

inductive star_cfg (cfg : SpuriousCfg) : config → List event → config → Prop
  | star_cfg_refl : ∀ c, star_cfg cfg c [] c
  | star_cfg_step : ∀ c1 evs c2 tr c3,
      sstep_cfg segs cfg c1 evs (SNext c2) →
      star_cfg cfg c2 tr c3 →
      star_cfg cfg c1 (evs ++ tr) c3

theorem star_cfg_sub (cfg : SpuriousCfg) (c : config) (tr : List event) (c' : config) :
    star_cfg segs cfg c tr c' → star segs c tr c' := by
  intro h
  induction h with
  | star_cfg_refl c => exact star.star_refl c
  | star_cfg_step c1 evs c2 tr c3 hs _ ih =>
    exact star.star_step c1 evs c2 tr c3 (sstep_cfg_sub segs cfg c1 evs (SNext c2) hs) ih

theorem star_cfg_may_fail (c : config) (tr : List event) (c' : config) :
    star segs c tr c' ↔ star_cfg segs may_fail_cfg c tr c' := by
  constructor
  · intro h
    induction h with
    | star_refl c => exact star_cfg.star_cfg_refl c
    | star_step c1 evs c2 tr c3 hs _ ih =>
      exact star_cfg.star_cfg_step c1 evs c2 tr c3
        ((sstep_cfg_may_fail segs c1 evs (SNext c2)).1 hs) ih
  · exact star_cfg_sub segs may_fail_cfg c tr c'

def obs_trace_cfg (cfg : SpuriousCfg) (c0 : config) (tr : List event) : Prop :=
  ∃ tr' c, star_cfg segs cfg c0 tr' c ∧ is_prefix tr tr'

def reaches_error_cfg (cfg : SpuriousCfg) (c0 : config) : Prop :=
  ∃ tr c evs, star_cfg segs cfg c0 tr c ∧ sstep_cfg segs cfg c evs SError

inductive all_traces_error_cfg (cfg : SpuriousCfg) : config → Prop
  | all_traces_error_cfg_intro : ∀ c,
      (∃ evs to, sstep_cfg segs cfg c evs to) →
      (∀ evs c', sstep_cfg segs cfg c evs (SNext c') → all_traces_error_cfg cfg c') →
      all_traces_error_cfg cfg c

def reaches_unmodeled_cfg (cfg : SpuriousCfg) (c0 : config) : Prop :=
  ∃ tr c, star_cfg segs cfg c0 tr c ∧ unmodeled_at segs c

/-- The filtered run removes executions and adds none: every trace, error
and uncovered point of the filtered run is one of the run's.
`all_traces_error_cfg` is deliberately absent from this list — it is a
universal over successors, so fewer steps do not give it in either direction
— and `Equivalence.equiv`'s escape is stated on it, which is one more reason
a proof at one configuration says nothing at another. -/
theorem obs_trace_cfg_sub (cfg : SpuriousCfg) (c0 : config) (tr : List event) :
    obs_trace_cfg segs cfg c0 tr → obs_trace segs c0 tr := by
  rintro ⟨tr', c, hs, hp⟩
  exact ⟨tr', c, star_cfg_sub segs cfg c0 tr' c hs, hp⟩

theorem reaches_error_cfg_sub (cfg : SpuriousCfg) (c0 : config) :
    reaches_error_cfg segs cfg c0 → reaches_error segs c0 := by
  rintro ⟨tr, c, evs, hs, he⟩
  exact ⟨tr, c, evs, star_cfg_sub segs cfg c0 tr c hs, sstep_cfg_sub segs cfg c evs SError he⟩

theorem reaches_unmodeled_cfg_sub (cfg : SpuriousCfg) (c0 : config) :
    reaches_unmodeled_cfg segs cfg c0 → reaches_unmodeled segs c0 := by
  rintro ⟨tr, c, hs, hu⟩
  exact ⟨tr, c, star_cfg_sub segs cfg c0 tr c hs, hu⟩

/-- …and at `may_fail_cfg` each of the four is the unfiltered one. -/
theorem obs_trace_cfg_may_fail (c0 : config) (tr : List event) :
    obs_trace segs c0 tr ↔ obs_trace_cfg segs may_fail_cfg c0 tr := by
  constructor
  · rintro ⟨tr', c, hs, hp⟩
    exact ⟨tr', c, (star_cfg_may_fail segs c0 tr' c).1 hs, hp⟩
  · rintro ⟨tr', c, hs, hp⟩
    exact ⟨tr', c, (star_cfg_may_fail segs c0 tr' c).2 hs, hp⟩

theorem reaches_error_cfg_may_fail (c0 : config) :
    reaches_error segs c0 ↔ reaches_error_cfg segs may_fail_cfg c0 := by
  constructor
  · rintro ⟨tr, c, evs, hs, he⟩
    exact ⟨tr, c, evs, (star_cfg_may_fail segs c0 tr c).1 hs,
      (sstep_cfg_may_fail segs c evs SError).1 he⟩
  · rintro ⟨tr, c, evs, hs, he⟩
    exact ⟨tr, c, evs, (star_cfg_may_fail segs c0 tr c).2 hs,
      (sstep_cfg_may_fail segs c evs SError).2 he⟩

theorem all_traces_error_cfg_may_fail (c : config) :
    all_traces_error segs c ↔ all_traces_error_cfg segs may_fail_cfg c := by
  constructor
  · intro h
    induction h with
    | all_traces_error_intro c hprog _ ih =>
      obtain ⟨evs, to, hstep⟩ := hprog
      refine all_traces_error_cfg.all_traces_error_cfg_intro c
        ⟨evs, to, (sstep_cfg_may_fail segs c evs to).1 hstep⟩ ?_
      intro evs' c' hss
      exact ih evs' c' ((sstep_cfg_may_fail segs c evs' (SNext c')).2 hss)
  · intro h
    induction h with
    | all_traces_error_cfg_intro c hprog _ ih =>
      obtain ⟨evs, to, hstep⟩ := hprog
      refine all_traces_error.all_traces_error_intro c
        ⟨evs, to, (sstep_cfg_may_fail segs c evs to).2 hstep⟩ ?_
      intro evs' c' hss
      exact ih evs' c' ((sstep_cfg_may_fail segs c evs' (SNext c')).1 hss)

theorem reaches_unmodeled_cfg_may_fail (c0 : config) :
    reaches_unmodeled segs c0 ↔ reaches_unmodeled_cfg segs may_fail_cfg c0 := by
  constructor
  · rintro ⟨tr, c, hs, hu⟩
    exact ⟨tr, c, (star_cfg_may_fail segs c0 tr c).1 hs, hu⟩
  · rintro ⟨tr, c, hs, hu⟩
    exact ⟨tr, c, (star_cfg_may_fail segs c0 tr c).2 hs, hu⟩

/-- Being uncovered is a special case of erroring under every configuration,
as it is under none: both uncovered shapes are premises of an `SError`
transition that no filter touches. -/
theorem reaches_unmodeled_cfg_reaches_error_cfg (cfg : SpuriousCfg) (c0 : config) :
    reaches_unmodeled_cfg segs cfg c0 → reaches_error_cfg segs cfg c0 := by
  rintro ⟨tr, ⟨ms, model⟩, hstar, hh, (⟨hsvc, hacc⟩ | ⟨x8, hsvc, hspec⟩)⟩
  · exact ⟨tr, config.mkCfg ms model, [], hstar,
      sstep_cfg.sstep_cfg_instr_unmodeled ms model hh hsvc hacc⟩
  · exact ⟨tr, config.mkCfg ms model, [], hstar,
      sstep_cfg.sstep_cfg_syscall_unmodeled ms model x8 hh hsvc hspec⟩

theorem all_traces_error_cfg_reaches_error_cfg (cfg : SpuriousCfg) (c : config) :
    all_traces_error_cfg segs cfg c → reaches_error_cfg segs cfg c := by
  intro hall
  induction hall with
  | all_traces_error_cfg_intro c hprog _ ih =>
    obtain ⟨evs, to, hstep⟩ := hprog
    cases to with
    | SNext c' =>
      obtain ⟨tr, c2, err_evs, hstar, herr⟩ := ih evs c' hstep
      exact ⟨evs ++ tr, c2, err_evs, star_cfg.star_cfg_step _ _ _ _ _ hstep hstar, herr⟩
    | SError => exact ⟨[], c, evs, star_cfg.star_cfg_refl c, hstep⟩

end StepCfg

/-- `run` under a spurious-failure configuration: the same initial
configuration, the same four observations, over the filtered step relation.
Written with projections, as `run` is, and for the same reason. -/
def run_scfg (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    behavior :=
  let c0 := init_config img.img_segments img.img_init_pc img.img_phdrs
              en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp
  { bh_traces := obs_trace_cfg img.img_segments cfg c0,
    bh_errors := reaches_error_cfg img.img_segments cfg c0,
    bh_all_errors := all_traces_error_cfg img.img_segments cfg c0,
    bh_unmodeled := reaches_unmodeled_cfg img.img_segments cfg c0 }

/-- Two behaviors that agree observation by observation.  `behavior` is a
record of bare `Prop`s, so this is the relation under which `run` and
`run_scfg may_fail_cfg` are the same thing — propositional equality of the
records would need propositional extensionality, which neither tree
assumes. -/
def behavior_equiv (b1 b2 : behavior) : Prop :=
  (∀ tr, b1.bh_traces tr ↔ b2.bh_traces tr)
  ∧ (b1.bh_errors ↔ b2.bh_errors)
  ∧ (b1.bh_all_errors ↔ b2.bh_all_errors)
  ∧ (b1.bh_unmodeled ↔ b2.bh_unmodeled)

theorem behavior_equiv_refl (b : behavior) : behavior_equiv b b :=
  ⟨fun _ => Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem behavior_equiv_sym (b1 b2 : behavior) :
    behavior_equiv b1 b2 → behavior_equiv b2 b1 := by
  rintro ⟨ht, he, ha, hu⟩
  exact ⟨fun tr => (ht tr).symm, he.symm, ha.symm, hu.symm⟩

/-- MEANING PRESERVED: `run_scfg may_fail_cfg` is `run`, observation by
observation.  This is what lets every statement above this section keep its
text: it is the `may_fail_cfg` instance of its `_scfg` form. -/
theorem run_scfg_may_fail (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    behavior_equiv (run_scfg may_fail_cfg img lim en inp) (run img lim en inp) :=
  ⟨fun tr => (obs_trace_cfg_may_fail _ _ tr).symm,
   (reaches_error_cfg_may_fail _ _).symm,
   (all_traces_error_cfg_may_fail _ _).symm,
   (reaches_unmodeled_cfg_may_fail _ _).symm⟩

/-- The run with every avoidable allocation refusal removed and every other
family as it always was: issue #570's `alloc_may_fail = false`. -/
def run_nospurious (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : behavior :=
  run_scfg (alloc_only_cfg false) img lim en inp

/-- Issue #570's one-switch form.  Written as an `if` on the literal so that
`run_cfg true` is `run` BY CONVERSION — every statement and library lemma
about `run` applies to the `true` instance with no bridge — and
`run_cfg false` is `run_nospurious`.  A proof stated over `run_cfg b` for a
variable `b` reaches the record form through `run_cfg_scfg`. -/
def run_cfg (alloc_may_fail : Bool) (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : behavior :=
  if alloc_may_fail then run img lim en inp else run_nospurious img lim en inp

theorem run_cfg_true (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    run_cfg true img lim en inp = run img lim en inp := rfl

theorem run_cfg_false (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    run_cfg false img lim en inp = run_nospurious img lim en inp := rfl

theorem run_cfg_scfg (b : Bool) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    behavior_equiv (run_cfg b img lim en inp) (run_scfg (alloc_only_cfg b) img lim en inp) := by
  cases b with
  | true => exact behavior_equiv_sym _ _ (run_scfg_may_fail img lim en inp)
  | false => exact behavior_equiv_refl _

/-- SUBSET, at the level of behaviors: whatever the configuration, the
filtered run's traces, errors and uncovered points are the run's. -/
theorem run_scfg_sub_traces (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) (tr : List event) :
    (run_scfg cfg img lim en inp).bh_traces tr → (run img lim en inp).bh_traces tr :=
  fun h => obs_trace_cfg_sub _ cfg _ tr h

theorem run_scfg_sub_errors (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) :
    (run_scfg cfg img lim en inp).bh_errors → (run img lim en inp).bh_errors :=
  fun h => reaches_error_cfg_sub _ cfg _ h

theorem run_scfg_sub_unmodeled (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) :
    (run_scfg cfg img lim en inp).bh_unmodeled → (run img lim en inp).bh_unmodeled :=
  fun h => reaches_unmodeled_cfg_sub _ cfg _ h

/-- The behavior-level images of the two containments `run` realises,
restated for the filtered run so that `Equivalence.error_free` keeps
subsuming `Equivalence.modeled` under every configuration. -/
theorem run_scfg_unmodeled_errors (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    (run_scfg cfg img lim en inp).bh_unmodeled → (run_scfg cfg img lim en inp).bh_errors :=
  fun h => reaches_unmodeled_cfg_reaches_error_cfg _ cfg _ h

theorem run_scfg_all_errors_errors (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    (run_scfg cfg img lim en inp).bh_all_errors → (run_scfg cfg img lim en inp).bh_errors :=
  fun h => all_traces_error_cfg_reaches_error_cfg _ cfg _ h

/-! ## The budget mark: where a run is refused for exceeding its budget

A PREDICATE over the configurations a run reaches — not a trace event,
which would enter trace equality, and not a state flag, which nothing
could set on the first-touch path, where the refusal IS the error
transition.  A configuration is budget-refused when the run is about to
be declined for exceeding `State.vm_limit`, in one of three ways: the
pending INSTRUCTION touches a lazy page the budget cannot back (the
interpreter answers `MachineOk` and `State.materialize_model_accesses`
answers `none`, so a `MachineFault` of the interpreter's own is NOT
budget-refused although both go to `SError`); the pending SYSCALL is a
grant the budget refuses (`alloc_budget_refused_b` on the request and the
pre-state, never the answer); or some admissible outcome of the pending
syscall has an effect whose copy-in or copy-out touches a lazy page the
budget cannot back.  The first and third are premises of an `SError`
transition; the second is not an error at all — the program is answered
-ENOMEM and goes on — which is why the premise is a separate observable
rather than a reading of `bh_errors`.  On a run with no MAP_NORESERVE
mapping `State.m_vm_lazy` is empty at every reachable state and the two
first-touch clauses are false, so discharging the premise is the grant
clause at each ecall.  The argument in full, including what
`Equivalence.strong_universal_T_budgets` states with it, is on the Rocq
`Run.budget_refused_at`.  Rocq's `Section Budget` variable `segs` is the
explicit first argument here, as `sstep` and `star` take it. -/
section Budget

variable (segs : List Segment)

def budget_refused_at (c : config) : Prop :=
  m_halted c.cfg_model = none ∧
  ( (c.cfg_ms.ms_svc_pending = none ∧
       ∃ report, step_accesses segs c.cfg_ms = MachineOk report ∧
         materialize_model_accesses c.cfg_model report.accessed_ranges = none)
    ∨ (∃ x8, c.cfg_ms.ms_svc_pending = some x8 ∧
         ( alloc_budget_refused_b (sys_input segs c.cfg_ms x8) c.cfg_model = true
         ∨ ∃ eff model' evs,
             syscall_spec (sys_input segs c.cfg_ms x8) c.cfg_model (Ok eff model' evs)
             ∧ m_halted model' = none
             ∧ materialize_model_accesses model' (syscall_effect_accesses eff) = none)) )

/-- The run can reach a budget-refused configuration. -/
def reaches_budget_refused (c0 : config) : Prop :=
  ∃ tr c, star segs c0 tr c ∧ budget_refused_at segs c

theorem reaches_budget_refused_intro (c : config) :
    budget_refused_at segs c → reaches_budget_refused segs c :=
  fun h => ⟨[], c, star.star_refl c, h⟩

theorem reaches_budget_refused_star (c0 : config) (tr : List event) (c : config) :
    star segs c0 tr c → reaches_budget_refused segs c → reaches_budget_refused segs c0 := by
  rintro hstar ⟨tr', c', hstar', hb⟩
  exact ⟨tr ++ tr', c', star_trans segs c0 tr c tr' c' hstar hstar', hb⟩

/-- The two first-touch clauses are premises of an error transition. -/
theorem budget_fault_instr_sstep_error (ms : machine_state) (model : Model)
    (report : access_report machine_state) :
    m_halted model = none →
    ms.ms_svc_pending = none →
    step_accesses segs ms = MachineOk report →
    materialize_model_accesses model report.accessed_ranges = none →
    sstep segs (config.mkCfg ms model) [] SError := by
  intro hh hsvc hstep hmat
  apply sstep.sstep_instr_fault ms model hh hsvc
  unfold mi_account_step
  simp only [hstep, hmat]

theorem budget_fault_syscall_sstep_error (ms : machine_state) (model : Model) (x8 : word)
    (eff : SyscallEffect) (model' : Model) (evs : List event) :
    m_halted model = none →
    ms.ms_svc_pending = some x8 →
    syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
    m_halted model' = none →
    materialize_model_accesses model' (syscall_effect_accesses eff) = none →
    sstep segs (config.mkCfg ms model) [] SError :=
  fun hh hsvc hspec hh' hmat =>
    sstep.sstep_syscall_materialization_fault ms model x8 eff model' evs hh hsvc hspec hh' hmat

/-- Discharging the premise: an invariant of the reachable configurations
that excludes the mark. -/
theorem star_invariant (I : config → Prop)
    (hstep : ∀ c evs c', I c → sstep segs c evs (SNext c') → I c') :
    ∀ c0 tr c, star segs c0 tr c → I c0 → I c := by
  intro c0 tr c hstar
  induction hstar with
  | star_refl c => exact fun h => h
  | star_step c1 evs c2 tr c3 hss _ ih => exact fun h1 => ih (hstep _ _ _ h1 hss)

theorem never_budget_refused_ind (I : config → Prop) (c0 : config) :
    I c0 →
    (∀ c evs c', I c → sstep segs c evs (SNext c') → I c') →
    (∀ c, I c → ¬ budget_refused_at segs c) →
    ¬ reaches_budget_refused segs c0 := by
  rintro h0 hstep hno ⟨tr, c, hstar, hb⟩
  exact hno c (star_invariant segs I hstep c0 tr c hstar h0) hb

/-- With no lazy mapping, an instruction configuration is never
budget-refused: the first-touch clause needs `none` where
`materialize_model_accesses_no_lazy` answers `some`, and the other two
need a pending syscall. -/
theorem budget_refused_at_no_lazy_instr (ms : machine_state) (model : Model) :
    m_vm_lazy model = [] →
    ms.ms_svc_pending = none →
    ¬ budget_refused_at segs (config.mkCfg ms model) := by
  rintro hlazy hsvc ⟨_, (⟨_, report, _, hmat⟩ | ⟨x8, hx8, _⟩)⟩
  · have hsome := materialize_model_accesses_no_lazy model report.accessed_ranges hlazy
    exact nomatch (hsome.symm.trans hmat)
  · exact nomatch (hsvc.symm.trans hx8)

/-- …and a syscall configuration whose every outcome leaves no lazy
mapping either is budget-refused exactly by the grant clause. -/
theorem budget_refused_at_no_lazy_syscall (ms : machine_state) (model : Model) (x8 : word) :
    m_halted model = none →
    ms.ms_svc_pending = some x8 →
    (∀ eff model' evs,
       syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) → m_vm_lazy model' = []) →
    (budget_refused_at segs (config.mkCfg ms model)
      ↔ alloc_budget_refused_b (sys_input segs ms x8) model = true) := by
  intro hh hsvc hlazy
  constructor
  · rintro ⟨_, (⟨hnone, _⟩ | ⟨y8, hy8, (hb | ⟨eff, model', evs, hspec, _, hmat⟩)⟩)⟩
    · exact nomatch (hsvc.symm.trans hnone)
    · have hxy : x8 = y8 := Option.some.inj (hsvc.symm.trans hy8)
      subst hxy
      exact hb
    · have hxy : x8 = y8 := Option.some.inj (hsvc.symm.trans hy8)
      subst hxy
      have hsome := materialize_model_accesses_no_lazy model' (syscall_effect_accesses eff)
                      (hlazy _ _ _ hspec)
      exact nomatch (hsome.symm.trans hmat)
  · intro hb
    exact ⟨hh, Or.inr ⟨x8, hsvc, Or.inl hb⟩⟩

/-- The same reachability under a configuration: `star_cfg` in place of
`star`, the mark unchanged.  The mark's instruction and grant clauses read
the state and the request and see no configuration; its effect clause
ranges over ALL the arm's admitted outcomes, including ones the
configuration filters out, so under a configuration that clause can fire on
the materialization fault of an outcome the configured run never takes — an
over-approximation of "the configured run is about to be refused", in the
safe direction (the premise is false more often, never true wrongly).  What
the configuration changes otherwise is WHICH configurations the run
reaches: fewer, never more (`reaches_budget_refused_cfg_sub`), so the
unfiltered premise discharges the configured one, and at `may_fail_cfg` the
configured reachability is the unfiltered one
(`reaches_budget_refused_cfg_may_fail`).  Where the GRANT clause fires on a
brk, mmap or mprotect request, the filter removes nothing at all — every
admitted outcome is a refusal, so none is spurious.  Not for mremap: its
mark fires when either of a grow's budget gates refuses, the in-place
post-state's or the move's, so it can fire where a move is still admitted,
and under a forced-only configuration the refusal it marks can be spurious
and the filter drops that step; the marked configuration is still reached,
so the premise is unaffected, and the mark stays an over-approximation in
the safe direction there.  Rocq pins both halves in
`Checks/BudgetPremise.v` (`marked_step_is_configured`,
`ov_mark_fires_while_a_move_fits`), which this tree has not ported. -/
def reaches_budget_refused_cfg (cfg : SpuriousCfg) (c0 : config) : Prop :=
  ∃ tr c, star_cfg segs cfg c0 tr c ∧ budget_refused_at segs c

theorem reaches_budget_refused_cfg_sub (cfg : SpuriousCfg) (c0 : config) :
    reaches_budget_refused_cfg segs cfg c0 → reaches_budget_refused segs c0 := by
  rintro ⟨tr, c, hstar, hb⟩
  exact ⟨tr, c, star_cfg_sub segs cfg c0 tr c hstar, hb⟩

theorem reaches_budget_refused_cfg_may_fail (c0 : config) :
    reaches_budget_refused segs c0 ↔ reaches_budget_refused_cfg segs may_fail_cfg c0 := by
  constructor
  · rintro ⟨tr, c, hstar, hb⟩
    exact ⟨tr, c, (star_cfg_may_fail segs c0 tr c).1 hstar, hb⟩
  · rintro ⟨tr, c, hstar, hb⟩
    exact ⟨tr, c, (star_cfg_may_fail segs c0 tr c).2 hstar, hb⟩

end Budget

/-- The run-level form: on the same initial configuration as `run`, with
the same use of projections where Rocq matches on the image and the
entry.  Rocq's `Equivalence.source_within_budget` negates it; the
budget-parameterised families of `Equivalence.v` are not ported. -/
def run_budget_refused (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  reaches_budget_refused img.img_segments
    (init_config img.img_segments img.img_init_pc img.img_phdrs
       en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

/-- The configured run's form, on the initial configuration of `run_scfg`. -/
def run_scfg_budget_refused (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  reaches_budget_refused_cfg img.img_segments cfg
    (init_config img.img_segments img.img_init_pc img.img_phdrs
       en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

theorem run_scfg_budget_refused_sub (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    run_scfg_budget_refused cfg img lim en inp → run_budget_refused img lim en inp :=
  fun h => reaches_budget_refused_cfg_sub _ cfg _ h

theorem run_scfg_budget_refused_may_fail (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) :
    run_budget_refused img lim en inp ↔ run_scfg_budget_refused may_fail_cfg img lim en inp :=
  reaches_budget_refused_cfg_may_fail _ _

/-! ## Valid process inputs -/

/-- Any 16-byte-aligned address in `[sp_window_lo, sp_window_hi]`. -/
def valid_sp (sp : word) : Prop :=
  sp_window_lo ≤ bv_unsigned sp ∧ bv_unsigned sp ≤ sp_window_hi ∧
  bv_unsigned sp % 16 = 0

/-- Any page-aligned address from the page-rounded image top up to
`brk_aslr_max` above it. -/
def valid_brk (segs : List Segment) (brk : word) : Prop :=
  reserved_top (segments_reserved segs) ≤ bv_unsigned brk
  ∧ bv_unsigned brk ≤ reserved_top (segments_reserved segs) + brk_aslr_max
  ∧ bv_unsigned brk % page_size = 0

def valid_mmap_base (mbase : word) : Prop :=
  mmap_base_min ≤ bv_unsigned mbase
  ∧ bv_unsigned mbase ≤ mmap_base_max
  ∧ bv_unsigned mbase % page_size = 0

/-- The same predicates for a DECLARED address-space size (`State.VaSize`);
`valid_sp` and `valid_mmap_base` above are the Sv48 instances in the
literal numbers. -/
def valid_sp_va (v : VaSize) (sp : word) : Prop :=
  va_sp_window_lo v ≤ bv_unsigned sp ∧ bv_unsigned sp ≤ va_sp_window_hi v ∧
  bv_unsigned sp % 16 = 0

def valid_mmap_base_va (v : VaSize) (mbase : word) : Prop :=
  va_mmap_base_min v ≤ bv_unsigned mbase
  ∧ bv_unsigned mbase ≤ va_mmap_base_max v
  ∧ bv_unsigned mbase % page_size = 0

theorem valid_sp_va_sv48 (sp : word) : valid_sp_va .Sv48 sp ↔ valid_sp sp := by
  simp only [valid_sp_va, valid_sp, va_sp_window_lo, va_sp_window_hi, va_stack_top,
    sp_window_lo, sp_window_hi]
  omega

theorem valid_mmap_base_va_sv48 (mb : word) : valid_mmap_base_va .Sv48 mb ↔ valid_mmap_base mb := by
  simp only [valid_mmap_base_va, valid_mmap_base, va_mmap_base_min, va_mmap_base_max,
    va_stack_top, mmap_base_max, mmap_base_min, sp_window_hi]

/-- Total bytes consumed by a list of argument strings (each length + 1
for the null terminator). -/
def total_arg_bytes (args : List (List byte)) : Int :=
  args.foldr (fun a acc => (a.length : Int) + 1 + acc) 0

/-- Validity predicate for argv lists.  At least one argument is required:
modern Linux never delivers argc = 0 (kernel commit dcd46d897adb rewrites
an empty `execve` argv to a single empty string).  The fifth clause is NOT
a fact about Linux: it narrows the theorem's domain so the whole-program
examples cannot reach `openat`'s separator decline; the argument and its
cost are on the Rocq definition and in
`bugs/valid-argv-excludes-slash-and-dotdot.md`. -/
def valid_argv (argv : List (List byte)) : Prop :=
  (1 ≤ (argv.length : Int) ∧ (argv.length : Int) ≤ 1024) ∧
  total_arg_bytes argv ≤ 2097152 ∧
  (∀ a ∈ argv, (a.length : Int) ≤ 131071) ∧
  (∀ a ∈ argv, ¬ (Z_to_bv 8 0) ∈ a) ∧
  (∀ a ∈ argv.tail, path_has_slash a = false ∧ path_eqb a dotdot_path = false)

def valid_envp (envp : List (List byte)) : Prop :=
  (envp.length : Int) ≤ 256 ∧
  total_arg_bytes envp ≤ 131072 ∧
  (∀ e ∈ envp, (e.length : Int) ≤ 131071) ∧
  (∀ e ∈ envp, ¬ (Z_to_bv 8 0) ∈ e)

/-- An upper bound on the entry stack image's length, in this file's own
vocabulary. -/
def entry_stack_span (argv envp : List (List byte)) : Int :=
  8                                     -- argc
  + 8 * (argv.length : Int) + 8         -- argv[] and its NULL
  + 8 * (envp.length : Int) + 8         -- envp[] and its NULL
  + (auxv_size : Int)                   -- the serialized auxv
  + total_arg_bytes argv                -- the argument strings
  + total_arg_bytes envp                -- the environment strings
  + 7                                   -- 8-alignment padding
  + 16                                  -- the AT_RANDOM block

/-- The entry stack image fits inside the user address space. -/
def entry_stack_fits (sp : word) (argv envp : List (List byte)) : Prop :=
  bv_unsigned sp + entry_stack_span argv envp ≤ sp_window_hi

/-- The same ceiling under a declared size: `STACK_TOP`, not `TASK_SIZE`. -/
def entry_stack_fits_va (v : VaSize) (sp : word) (argv envp : List (List byte)) : Prop :=
  bv_unsigned sp + entry_stack_span argv envp ≤ va_sp_window_hi v

theorem entry_stack_fits_va_sv48 (sp : word) (argv envp : List (List byte)) :
    entry_stack_fits_va .Sv48 sp argv envp ↔ entry_stack_fits sp argv envp := by
  simp only [entry_stack_fits_va, entry_stack_fits, va_sp_window_hi, va_stack_top]

def entry_stack_span_max : Int := 2238671

theorem total_arg_bytes_nonneg (args : List (List byte)) : 0 ≤ total_arg_bytes args := by
  induction args with
  | nil => simp [total_arg_bytes]
  | cons a r ih =>
    simp only [total_arg_bytes, List.foldr] at ih ⊢
    have : (0 : Int) ≤ (a.length : Int) := by exact_mod_cast Nat.zero_le _
    omega

theorem entry_stack_span_bound (argv envp : List (List byte)) :
    valid_argv argv → valid_envp envp →
    0 ≤ entry_stack_span argv envp ∧ entry_stack_span argv envp ≤ entry_stack_span_max := by
  rintro ⟨⟨_, hla⟩, hta, _⟩ ⟨hle, hte, _⟩
  have h1 := total_arg_bytes_nonneg argv
  have h2 := total_arg_bytes_nonneg envp
  have h3 : (0 : Int) ≤ (argv.length : Int) := by exact_mod_cast Nat.zero_le _
  have h4 : (0 : Int) ≤ (envp.length : Int) := by exact_mod_cast Nat.zero_le _
  unfold entry_stack_span entry_stack_span_max auxv_size
  omega

/-- What `execve` may hand this binary ON THIS INPUT, under a declared
address-space size: the window is the declared kernel's. -/
def valid_entry_va (v : VaSize) (img : Image) (en : ExecEntry) (inp : ProcInput) : Prop :=
  valid_sp_va v en.en_sp ∧ valid_brk img.img_segments en.en_brk
  ∧ valid_mmap_base_va v en.en_mmap_base
  ∧ entry_stack_fits_va v en.en_sp inp.in_argv inp.in_envp

/-- What `execve` may hand this binary ON THIS INPUT: the size is read off
the input. -/
def valid_entry (img : Image) (en : ExecEntry) (inp : ProcInput) : Prop :=
  valid_entry_va inp.in_va_size img en inp

/-- Under an Sv48 input the predicate is the literal Sv48 one, conjunct for
conjunct. -/
theorem valid_entry_sv48 (img : Image) (en : ExecEntry) (inp : ProcInput)
    (h : inp.in_va_size = .Sv48) :
    valid_entry img en inp
    ↔ (valid_sp en.en_sp ∧ valid_brk img.img_segments en.en_brk
        ∧ valid_mmap_base en.en_mmap_base
        ∧ entry_stack_fits en.en_sp inp.in_argv inp.in_envp) := by
  unfold valid_entry valid_entry_va
  rw [h, valid_sp_va_sv48, valid_mmap_base_va_sv48, entry_stack_fits_va_sv48]

/-- An id is a 32-BIT value, and `(uid_t)-1` is `INVALID_UID`
(kernel/user_namespace.c `make_kuid`, Linux v6.18.46, commit 1f99e9ab748f). -/
def valid_id (u : word) : Prop := bv_unsigned u < 2 ^ 32 - 1

def valid_creds (inp : ProcInput) : Prop :=
  valid_id inp.in_uid ∧ valid_id inp.in_gid

/-- The soft RLIMIT_NOFILE a launch can really carry: at most
`sysctl_nr_open_max` = 2^31 - 64 on LP64 (fs/file.c; kernel/sys.c
`do_prlimit`, Linux v6.18.46, commit 1f99e9ab748f). -/
def valid_nofile (n : word) : Prop := bv_unsigned n ≤ 2 ^ 31 - 64

/-- SIGKILL and SIGSTOP are never in the blocked mask a process is STARTED
with.  Every path that leaves a mask on a task returning to userspace
strips the two bits or cannot set them: `SYSCALL_DEFINE4(rt_sigprocmask)`
strips `new_set` itself and `set_current_blocked` strips for every other
caller (kernel/signal.c), `ptrace_setsigmask` strips (kernel/ptrace.c),
PID 1 starts from `init_task`'s zeroed `.blocked` (init/init_task.c) and
`fs/exec.c` never names the field — all at Linux v6.18.46, commit
1f99e9ab748f; the full enumeration, including the in-kernel windows that
do set them and restore on the next line, is on the Rocq definition.  An
absence argument, so it rots the way absence arguments do. -/
def valid_sigmask (inp : ProcInput) : Prop :=
  bv_and inp.in_sigmask (Z_to_bv 64 sig_kernel_only_mask) = Z_to_bv 64 0

/-- The same capability domain as `Run.valid_hwcap` in Rocq commit
7f386a77d4d3877f162c91f06b7e4fcc1d998e61; see its source argument there.
The word is a shared input rather than an entry draw for each binary. -/
def valid_hwcap (h : word) : Prop :=
  h = hwcap_rv64gc ∨ h = hwcap_rv64gcv

/-- THE RANDOM DEVICE'S DECLARED STREAM NEVER ENDS.  The one clause in
`valid_input` that is a FIX rather than a narrowing: /dev/urandom does not
run out, so a finite declaration describes no device at all.
`urandom_read_iter` is `get_random_bytes_user` over the imported iterator,
and that loops until the iterator is drained, stopping early only where
`copy_to_iter` copies short or a signal is pending at a page boundary
(drivers/char/random.c, Linux v6.18.46; both functions were read in the
6.12.1 tree on this box, where both are the same).  It says NOTHING
about the contents: only that a read yields as many bytes as it asked for,
which is what `Sys.Fs.ReadWrite.read_urandom`'s decline needs.  Rocq
`valid_urandom`. -/
def valid_urandom (inp : ProcInput) : Prop :=
  State.stream_infinite inp.in_urandom

def valid_input (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs inp.in_fs
  ∧ fs_image_real inp.in_image_fs = true
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap ∧ inp.in_abort_terminal = false
  ∧ inp.in_va_size = .Sv48 ∧ valid_urandom inp

/-- The SAME predicate with the abort-path declaration turned on, and a
separate definition rather than a parameter for the reason the two shapes of
every other statement in this tree are separate: what a proof was made under
has to be readable in the statement.

THE TWO PREDICATES ARE EXHAUSTIVE and mutually exclusive on the field:
`in_abort_terminal` is a `Bool`, so a statement that quantifies over
`valid_input` speaks about runs in which `tkill` (130) and `tgkill` (131) are
declined exactly as they were before either had an arm, a statement that
quantifies over `valid_input_abort` speaks about runs in which a SIGABRT the
process sends itself ends it, and a statement that pins neither —
quantifying over `valid_input_either` — asserts both
(`valid_input_either_splits`).  There is no third stance and no way to leave
the question open by accident, which is the whole point of the field being
in the input rather than in a configuration a checker might forget to
ascribe.

WHY `valid_input` IS THE ONE THAT PINS `false`.  Every statement written
before the abort path had an arm quantifies over `valid_input`, and pinning
the field there is what keeps those statements saying what they said: with
the declaration off, `tkill_spec` and `tgkill_spec` decline every call
(`Sys/Kernel/Signal.lean`), and under `decl_off_frame` no `KillEv` can
appear in any trace (`star_off_no_kill`).  A task that wants the other
reading asks for it by name. -/
def valid_input_abort (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs inp.in_fs
  ∧ fs_image_real inp.in_image_fs = true
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap ∧ inp.in_abort_terminal = true
  ∧ inp.in_va_size = .Sv48 ∧ valid_urandom inp

/-- Neither stance pinned: the clauses both share, and nothing about the
declaration.  A statement quantified over this one is the CONJUNCTION of the
two above — it has to hold whichever stance the task takes — which is what
makes forgetting to choose the safe failure rather than the dangerous
one. -/
def valid_input_either (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs inp.in_fs
  ∧ fs_image_real inp.in_image_fs = true
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap
  ∧ inp.in_va_size = .Sv48 ∧ valid_urandom inp

/-- The same predicate under each of the other two address-space sizes,
and the one that pins none; `valid_input` pins Sv48, the size every
statement in the tree was written against.  All three keep the abort
stance off, as in Rocq. -/
def valid_input_sv39 (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs inp.in_fs
  ∧ fs_image_real inp.in_image_fs = true
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap ∧ inp.in_abort_terminal = false
  ∧ inp.in_va_size = .Sv39 ∧ valid_urandom inp

def valid_input_sv57 (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs inp.in_fs
  ∧ fs_image_real inp.in_image_fs = true
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap ∧ inp.in_abort_terminal = false
  ∧ inp.in_va_size = .Sv57 ∧ valid_urandom inp

def valid_input_va_any (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs inp.in_fs
  ∧ fs_image_real inp.in_image_fs = true
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap ∧ inp.in_abort_terminal = false
  ∧ valid_urandom inp

/- NO PROOF BELOW REACHES INTO `valid_input` BY POSITION, mirroring the rule
above Rocq's `valid_input`.  The predicate and its variants grow a conjunct
whenever the input class learns to say something new, and a change can
land elsewhere first (#1005 inserts an image-keys clause right after
`valid_fs`), so a projection chain `h.2.2.2.….1` or an anonymous
constructor of today's arity merges onto the longer predicate without a
conflict: every projection past the insertion then names a different
clause, and fails to build only where the wrong clause does not fit.
Each proof instead splits the hypothesis into its clauses however many
there are (`repeat obtain ⟨_, h⟩ := (h : _ ∧ _)`), then splits the goal
the same way and closes each clause by its shape (`repeat' (first |
with_reducible assumption | refine ⟨?_, ?_⟩)`), the Lean form of Rocq's
`valid_input_clauses`: a clause it cannot find fails the proof, as an
elaboration error at the last alternative's `refine` (which `first` runs
with error recovery on), not a silent pass.  The ascription
`(h : _ ∧ _)` is load-bearing: `obtain` alone unfolds its target and
takes apart a LAST clause that rcases can destructure — a `True`, an
`∃`, an `∨`, or an `Eq` that `cases` closes outright such as
`(0 : Nat) = 0`, though not a projection-shaped one like
`inp.in_va_size = .Sv48` — which the goal side then cannot find, so a
single trailing insertion of such a clause broke four of the six proofs
that stood below when it was measured, without the ascription.  An insertion test that
puts the same `True` in the middle as well cannot see this: the middle
one closes the goal's trailing one.  Reducible transparency is
load-bearing too: a plain `assumption` compares a goal clause against
each hypothesis by full unfolding, newest first, and comparing the
`valid_envp` goal with the `valid_creds` hypothesis unfolds `valid_id`'s
`< 2 ^ 32 - 1` against `valid_envp`'s `≤ 256` until whnf unrolls
`Nat.sub` one step per unit of the literal; the recursion-depth error
aborts `assumption` outright rather than letting it try the next
hypothesis.  The clauses are syntactically the definition's own, so a
match needs no unfolding.  Written out rather than as a `macro` because
this file is one the budget-mark reader consults, and that reader
refuses a string literal. -/

theorem valid_input_va_size (inp : ProcInput) (h : valid_input inp) : inp.in_va_size = .Sv48 := by
  unfold valid_input at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-- The random-stream clause, read back by name rather than by position:
it is the LAST conjunct today, so a caller reaching in by position is the
first thing the next insertion breaks.  Rocq `valid_input_urandom`. -/
theorem valid_input_urandom (inp : ProcInput) (h : valid_input inp) :
    valid_urandom inp := by
  unfold valid_input at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-- The abort declaration, read back by name for the same reason: the
clause that makes `tkill_spec` and `tgkill_spec` decline every call under
`valid_input`.  Rocq `valid_input_abort_terminal`. -/
theorem valid_input_abort_terminal (inp : ProcInput) (h : valid_input inp) :
    inp.in_abort_terminal = false := by
  unfold valid_input at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-- The remaining clauses, each by name, so that no consumer is left with a
reason to reach in by position (the rule above `valid_input_va_size`).
Rocq `valid_input_argv` … `valid_input_hwcap`. -/
theorem valid_input_argv (inp : ProcInput) (h : valid_input inp) : valid_argv inp.in_argv := by
  unfold valid_input at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_envp (inp : ProcInput) (h : valid_input inp) : valid_envp inp.in_envp := by
  unfold valid_input at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_fs (inp : ProcInput) (h : valid_input inp) : valid_fs inp.in_fs := by
  unfold valid_input at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_image_real (inp : ProcInput) (h : valid_input inp) :
    fs_image_real inp.in_image_fs = true := by
  unfold valid_input at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_creds (inp : ProcInput) (h : valid_input inp) : valid_creds inp := by
  unfold valid_input at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_nofile (inp : ProcInput) (h : valid_input inp) :
    valid_nofile inp.in_nofile := by
  unfold valid_input at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_sigmask (inp : ProcInput) (h : valid_input inp) : valid_sigmask inp := by
  unfold valid_input at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_hwcap (inp : ProcInput) (h : valid_input inp) : valid_hwcap inp.in_hwcap := by
  unfold valid_input at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-- The same clause under the declared stance, where it is `true`. -/
theorem valid_input_abort_abort_terminal (inp : ProcInput) (h : valid_input_abort inp) :
    inp.in_abort_terminal = true := by
  unfold valid_input_abort at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-- Both abort stances pin the same size. -/
theorem valid_input_abort_va_size (inp : ProcInput) (h : valid_input_abort inp) :
    inp.in_va_size = .Sv48 := by
  unfold valid_input_abort at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-- The declared size under each of the other two predicates, by name, for
the reason `valid_input_va_size` is. -/
theorem valid_input_sv39_va_size (inp : ProcInput) (h : valid_input_sv39 inp) :
    inp.in_va_size = .Sv39 := by
  unfold valid_input_sv39 at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_sv57_va_size (inp : ProcInput) (h : valid_input_sv57 inp) :
    inp.in_va_size = .Sv57 := by
  unfold valid_input_sv57 at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_either_of_valid_input (inp : ProcInput) (h : valid_input inp) :
    valid_input_either inp := by
  unfold valid_input at h; unfold valid_input_either; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_either_of_valid_input_abort (inp : ProcInput) (h : valid_input_abort inp) :
    valid_input_either inp := by
  unfold valid_input_abort at h; unfold valid_input_either; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-- The exhaustiveness `valid_input_abort` claims, as a lemma rather than as
a sentence: an input the shared clauses accept satisfies one of the two
pinned predicates, because a `Bool` has two values. -/
theorem valid_input_either_splits (inp : ProcInput) (h : valid_input_either inp) :
    valid_input inp ∨ valid_input_abort inp := by
  unfold valid_input_either at h
  cases hab : inp.in_abort_terminal with
  | false => refine Or.inl ?_; unfold valid_input; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  | true => refine Or.inr ?_; unfold valid_input_abort; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_va_any_of_valid_input (inp : ProcInput) (h : valid_input inp) :
    valid_input_va_any inp := by
  unfold valid_input at h; unfold valid_input_va_any; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_va_any_of_valid_input_sv39 (inp : ProcInput) (h : valid_input_sv39 inp) :
    valid_input_va_any inp := by
  unfold valid_input_sv39 at h; unfold valid_input_va_any; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_va_any_of_valid_input_sv57 (inp : ProcInput) (h : valid_input_sv57 inp) :
    valid_input_va_any inp := by
  unfold valid_input_sv57 at h; unfold valid_input_va_any; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_va_any_splits (inp : ProcInput) (h : valid_input_va_any inp) :
    valid_input inp ∨ valid_input_sv39 inp ∨ valid_input_sv57 inp := by
  unfold valid_input_va_any at h
  cases hv : inp.in_va_size with
  | Sv39 => refine Or.inr (Or.inl ?_); unfold valid_input_sv39; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  | Sv48 => refine Or.inl ?_; unfold valid_input; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  | Sv57 => refine Or.inr (Or.inr ?_); unfold valid_input_sv57; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-- The TASK-DECLARED capability word, mirroring Rocq's
`valid_input_hwcap_rv64gc` / `valid_input_hwcap_rv64gcv`: `valid_input`'s
`valid_hwcap` clause replaced by the word itself.  The DEFAULT stays the
permissive disjunction — the model never claims the hart lacks V — and these
are what a task issues when it says which word its kernel publishes.  Named
definitions rather than a predicate parameterised by the word, for the reason
the Rocq side gives: a parameter could be instantiated at a word `valid_hwcap`
refuses, and the statement would then hold vacuously.  Both keep the abort
stance off and the size at Sv48, as the per-size predicates do. -/
def valid_input_hwcap_rv64gc (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs inp.in_fs
  ∧ fs_image_real inp.in_image_fs = true
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ inp.in_hwcap = hwcap_rv64gc ∧ inp.in_abort_terminal = false
  ∧ inp.in_va_size = .Sv48 ∧ valid_urandom inp

def valid_input_hwcap_rv64gcv (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs inp.in_fs
  ∧ fs_image_real inp.in_image_fs = true
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ inp.in_hwcap = hwcap_rv64gcv ∧ inp.in_abort_terminal = false
  ∧ inp.in_va_size = .Sv48 ∧ valid_urandom inp

theorem valid_input_of_valid_input_hwcap_rv64gc (inp : ProcInput)
    (h : valid_input_hwcap_rv64gc inp) : valid_input inp := by
  unfold valid_input_hwcap_rv64gc at h
  have hw : inp.in_hwcap = hwcap_rv64gc := by (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  have hg : valid_hwcap inp.in_hwcap := Or.inl hw
  unfold valid_input; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_of_valid_input_hwcap_rv64gcv (inp : ProcInput)
    (h : valid_input_hwcap_rv64gcv inp) : valid_input inp := by
  unfold valid_input_hwcap_rv64gcv at h
  have hw : inp.in_hwcap = hwcap_rv64gcv := by (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  have hg : valid_hwcap inp.in_hwcap := Or.inr hw
  unfold valid_input; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-- The default is EXACTLY the two, because `valid_hwcap` is a two-word
disjunction and nothing else in `valid_input` reads the field. -/
theorem valid_input_hwcap_splits (inp : ProcInput) (h : valid_input inp) :
    valid_input_hwcap_rv64gc inp ∨ valid_input_hwcap_rv64gcv inp := by
  unfold valid_input at h
  have hg : valid_hwcap inp.in_hwcap := by (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  unfold valid_hwcap at hg
  cases hg with
  | inl hw => refine Or.inl ?_; unfold valid_input_hwcap_rv64gc; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  | inr hw => refine Or.inr ?_; unfold valid_input_hwcap_rv64gcv; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-- The declared word, read back out of the predicate: `auxv_entries`
publishes `in_hwcap` verbatim, so this is WHICH word the auxv carries under
the declaration. -/
theorem valid_input_hwcap_rv64gc_word (inp : ProcInput) (h : valid_input_hwcap_rv64gc inp) :
    inp.in_hwcap = hwcap_rv64gc := by
  unfold valid_input_hwcap_rv64gc at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_hwcap_rv64gcv_word (inp : ProcInput) (h : valid_input_hwcap_rv64gcv inp) :
    inp.in_hwcap = hwcap_rv64gcv := by
  unfold valid_input_hwcap_rv64gcv at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-- The stance each declared word keeps, by name: the word declaration does
not carry the abort stance. -/
theorem valid_input_hwcap_rv64gc_abort_terminal (inp : ProcInput)
    (h : valid_input_hwcap_rv64gc inp) : inp.in_abort_terminal = false := by
  unfold valid_input_hwcap_rv64gc at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_hwcap_rv64gcv_abort_terminal (inp : ProcInput)
    (h : valid_input_hwcap_rv64gcv inp) : inp.in_abort_terminal = false := by
  unfold valid_input_hwcap_rv64gcv at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-! ### The same declaration under the ABORT stance

The two predicates above pin the abort declaration OFF, because that is the
stance `valid_input` pins and the one every statement written before the
abort path had an arm quantifies over.  A task whose binary probes for a
vector unit AND wants the abort path modeled needs the other cell: the
conjuncts of `valid_input_abort` verbatim, with `valid_hwcap inp.in_hwcap`
replaced by the equation.  The declaration crosses with the abort stance
and with nothing else, as in Rocq: `valid_input_either` gets no hwcap
predicate — a statement that declines to choose a stance is the conjunction
of the two that do — and neither do the per-size predicates. -/

def valid_input_abort_hwcap_rv64gc (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs inp.in_fs
  ∧ fs_image_real inp.in_image_fs = true
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ inp.in_hwcap = hwcap_rv64gc ∧ inp.in_abort_terminal = true
  ∧ inp.in_va_size = .Sv48 ∧ valid_urandom inp

def valid_input_abort_hwcap_rv64gcv (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs inp.in_fs
  ∧ fs_image_real inp.in_image_fs = true
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ inp.in_hwcap = hwcap_rv64gcv ∧ inp.in_abort_terminal = true
  ∧ inp.in_va_size = .Sv48 ∧ valid_urandom inp

theorem valid_input_abort_of_valid_input_abort_hwcap_rv64gc (inp : ProcInput)
    (h : valid_input_abort_hwcap_rv64gc inp) : valid_input_abort inp := by
  unfold valid_input_abort_hwcap_rv64gc at h
  have hw : inp.in_hwcap = hwcap_rv64gc := by (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  have hg : valid_hwcap inp.in_hwcap := Or.inl hw
  unfold valid_input_abort; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_abort_of_valid_input_abort_hwcap_rv64gcv (inp : ProcInput)
    (h : valid_input_abort_hwcap_rv64gcv inp) : valid_input_abort inp := by
  unfold valid_input_abort_hwcap_rv64gcv at h
  have hw : inp.in_hwcap = hwcap_rv64gcv := by (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  have hg : valid_hwcap inp.in_hwcap := Or.inr hw
  unfold valid_input_abort; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-- The capability clause under the abort stance, by name, for the split
below. -/
theorem valid_input_abort_hwcap (inp : ProcInput) (h : valid_input_abort inp) :
    valid_hwcap inp.in_hwcap := by
  unfold valid_input_abort at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_abort_hwcap_splits (inp : ProcInput) (h : valid_input_abort inp) :
    valid_input_abort_hwcap_rv64gc inp ∨ valid_input_abort_hwcap_rv64gcv inp := by
  have hg := valid_input_abort_hwcap inp h
  unfold valid_input_abort at h
  unfold valid_hwcap at hg
  cases hg with
  | inl hw => refine Or.inl ?_; unfold valid_input_abort_hwcap_rv64gc; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)
  | inr hw => refine Or.inr ?_; unfold valid_input_abort_hwcap_rv64gcv; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_abort_hwcap_rv64gc_word (inp : ProcInput)
    (h : valid_input_abort_hwcap_rv64gc inp) : inp.in_hwcap = hwcap_rv64gc := by
  unfold valid_input_abort_hwcap_rv64gc at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_abort_hwcap_rv64gcv_word (inp : ProcInput)
    (h : valid_input_abort_hwcap_rv64gcv inp) : inp.in_hwcap = hwcap_rv64gcv := by
  unfold valid_input_abort_hwcap_rv64gcv at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

/-- …and the stance each keeps, by name, the abort side of
`valid_input_hwcap_rv64gc_abort_terminal`. -/
theorem valid_input_abort_hwcap_rv64gc_abort_terminal (inp : ProcInput)
    (h : valid_input_abort_hwcap_rv64gc inp) : inp.in_abort_terminal = true := by
  unfold valid_input_abort_hwcap_rv64gc at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_input_abort_hwcap_rv64gcv_abort_terminal (inp : ProcInput)
    (h : valid_input_abort_hwcap_rv64gcv inp) : inp.in_abort_terminal = true := by
  unfold valid_input_abort_hwcap_rv64gcv at h; (repeat obtain ⟨_, h⟩ := (h : _ ∧ _)); repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

end LinuxProcessSemantics.LinuxProcessSem.Run
