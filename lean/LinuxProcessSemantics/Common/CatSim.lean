import LinuxProcessSemantics.LinuxProcessSem.Run
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
import LinuxProcessSemantics.Common.ExitSim

/-! # Common.CatSim — the write-syscall facts of the exit-after-writes library

Ported from `theories/Common/CatSim.v` at
2cde689f94c086b868999970834b76a25616b94a: the part of it `cat1024_ns`'s
`Proof.v` reaches (`Print All Dependencies` of its
`strong_universal`, ticket E-proof-library), with the Rocq statements.
That is the memory-read bridge (`read_aux_read_byte`,
`read_bytes_map_read_byte`), the no-write effect facts
(`apply_effect_no_write`, `apply_effect_copyins_no_write`), the write
number's dispatch (`in_mem_sys_input`, `syscall_spec_write`), the buffer
bound (`buf_modeled`, `buf_modeled_skipn`), `is_prefix_app_mono`, the
instruction-run relation `msteps` and its induction principle `msteps_ind`
(generated in Rocq, stated as a theorem here), and the channel-parametric write node (`fd1chan`, `fdchan`,
`fd1chan_fdchan`, `write_ch_check_n`, `write_ch_ok_n`, `write_ch_ok_inv`,
`write_ch_no_unmodeled`, `sstep_write_ch_inv`).

Everything else in the Rocq file was left unported by that ticket;
cat1024_ns reaches none of it.  Sections appended at the end of this file
since, each headed by the ticket that added it, port some of it.  What that
ticket left includes: the fd-1 write node and its inversion (`write1_*`,
`sstep_write_inv`), `bufs_modeled` and its lemmas, `buf_modeled_nil`, the
full-delivery event lists `wevents_ch` and `wevents`, the delivery-choice
relation `wpick`,
`to_wexit`/`to_wexit_ch` and every lemma over them, `msteps_one`,
`msteps_trans`, `init_model_fdchan2`, `init_model_fd1chan`, `wexit_post`,
the `in_*_sys_input64` projections, and the `cat_*`
observation/no-error/equivalence theorems.

Representation divergences, spelled Lean's way:
- Rocq `firstn`/`skipn` are `List.take`/`List.drop`, and `(_ <= _)%nat` is
  `Nat`'s `≤`.
- Rocq Section variables become explicit leading arguments: `msteps` takes
  `segs`, and `sstep_write_ch_inv` takes `segs fd ch` and the hypothesis
  `Hfd32 : fd32 fd = fd` ahead of its own binders, the order Rocq's
  `Section WithSegsCh` closes them in.

Universes.  Rocq's `is_prefix_app_mono` is not universe polymorphic, and
binds `A : Type@{is_prefix_app_mono.u0}`, a global universe.  Here it binds
`{A : Type}`, universe 0, because the `Run.is_prefix` its statement
applies binds `{A : Type}`, and a `Type _` binder is set to 0 there with
no error.  Rocq's `A` may also be a proposition, by cumulativity, or a
type Lean places above `Type`, such as `Type` itself, which a use admits
by bounding the lemma's global universe from below; Lean's may be neither.
`Prop`, `Nat → Prop` and `List Prop` are not among these: Rocq places them
above `Set`, Lean places them in `Type`, and both take them.  Widening the
binder needs a `lean: base:` change that widens `Run.is_prefix` first, and
the instances where Rocq's `A` is a proposition have no Lean form either
way. -/

namespace LinuxProcessSemantics.Common.CatSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite

/-! ## Memory-read bridge: `read_bytes_map` over `ms_read_byte` is `ms_read_bytes` -/

theorem read_aux_read_byte (ms : machine_state) (k : Nat) (a : word) :
    read_bytes_aux (ms_read_byte ms) a k = ms_read_bytes_aux ms a k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [read_bytes_aux, ms_read_bytes_aux, ih]
    cases ms_read_byte ms a <;> rfl

theorem read_bytes_map_read_byte (ms : machine_state) (a len : word) :
    read_bytes_map (ms_read_byte ms) a len = ms_read_bytes ms a len := by
  rw [read_bytes_map_eq]
  unfold ms_read_bytes
  exact read_aux_read_byte ms _ a

/-! ## `apply_effect` of a no-write effect just sets a0 -/

theorem apply_effect_no_write (ms : machine_state) (r : word) :
    apply_effect ms (mkEffect r [] []) = set_gpr0 ms r := rfl

theorem apply_effect_copyins_no_write (ms : machine_state) (r : word)
    (copyins : List (word × Nat)) :
    apply_effect ms (with_copyins copyins (mkEffect r [] [])) = set_gpr0 ms r := rfl

/-! ## Argument decoding for a write syscall input -/

theorem in_mem_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_mem = ms_read_byte ms := rfl

/-- Which arm answers this number, on the SPEC side.  `syscall_spec` is
`dispatch spec_table`, so fixing the number settles the table lookup by
conversion and the dispatcher disappears -- the same one-line argument
Rocq's `Checks.Sys.DispatchCompute` (unported) makes for `check_syscall`,
made here instead so that this file needs only the write checker rather
than the module that re-exports every arm's.  See #580. -/
theorem syscall_spec_write (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (o : LinuxProcessSemantics.LinuxProcessSem.Monad.outcome SyscallEffect)
    (hno : bv_unsigned x8 = 64) :
    syscall_spec (sys_input segs ms x8) model o ↔
      write_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
        (sys_input segs ms x8) model o := by
  have hx : (sys_input segs ms x8).in_sysno = x8 := rfl
  unfold syscall_spec dispatch
  rw [hx, hno]
  exact Iff.rfl

/-! ## fd 1 resolves to channel 1 -/

def fd1chan (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 1) = some (FdEntry.FdChannel (Z_to_bv 64 1))

/-- One buffer is at most `Uaccess.rw_bytes_max` bytes.  That discharges
the first disjunct of `write_spec`'s range gate `Uaccess.modeled_rw_range`
(`modeled_rw_count count || access_okb buf …`), so the gate passes whatever
the range.  The bound is sufficient for the gate and not necessary: the
second disjunct passes a larger buffer whose range `access_okb` accepts,
so Rocq's comment on `buf_modeled`, that `write_spec` is `unmodeled` above
the bound, is not carried over.  What the gate declines is the subject of
its own comment. -/
def buf_modeled (b : List byte) : Prop :=
  (b.length : Int) ≤ rw_bytes_max

/-- A retry loop reissues the write on the UNDELIVERED tail, so the
obligation has to survive `skipn` (Lean `List.drop`): a shorter buffer is
still one the model can judge. -/
theorem buf_modeled_skipn (n : Nat) (b : List byte) (H : buf_modeled b) :
    buf_modeled (b.drop n) := by
  unfold buf_modeled at *
  rw [List.length_drop]
  omega

/-! ## Prefix helpers -/

theorem is_prefix_app_mono {A : Type} (l a b : List A) (H : is_prefix a b) :
    is_prefix (l ++ a) (l ++ b) := by
  induction l with
  | nil => exact H
  | cons x l ih => exact ⟨rfl, ih⟩

-- These instances pin the header's accepted universe-0 types.
example := @is_prefix_app_mono Prop
example := @is_prefix_app_mono (Nat → Prop)
example := @is_prefix_app_mono (List Prop)

-- The `Type` refusal records the header's claim. Widening just this lemma's
-- binder to `Type _` elaborates at `Type` again: the statement's
-- `Run.is_prefix` is universe 0, so a real widening changes that constant too.
/-- error: Application type mismatch: The argument
  Type
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  @is_prefix_app_mono Type -/
#guard_msgs in
set_option pp.mvars false in
example := @is_prefix_app_mono Type

/-- error: Application type mismatch: The argument
  True
has type
  Prop
of sort `Type` but is expected to have type
  Type
of sort `Type 1` in the application
  @is_prefix_app_mono True -/
#guard_msgs in
set_option pp.mvars false in
example := @is_prefix_app_mono True

/-! ## `msteps`: a run of ordinary (non-syscall) instruction steps -/

inductive msteps (segs : List Segment) : machine_state → machine_state → Prop
  | mst_refl : ∀ ms, msteps segs ms ms
  | mst_step : ∀ ms ms' ms'',
      ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' →
      msteps segs ms' ms'' →
      msteps segs ms ms''

/-- Rocq's generated induction principle for `msteps`.  Lean generates no
non-dependent `_ind`: `msteps.rec`, and the `recOn`/`casesOn` built on it,
take a motive over the derivation, so it is stated here with the Rocq
statement. -/
theorem msteps_ind (segs : List Segment) (P : machine_state → machine_state → Prop)
    (f : ∀ ms, P ms ms)
    (f0 : ∀ ms ms' ms'', ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      msteps segs ms' ms'' → P ms' ms'' → P ms ms'') :
    ∀ m m0, msteps segs m m0 → P m m0 := by
  intro m m0 h
  induction h with
  | mst_refl ms => exact f ms
  | mst_step ms ms' ms'' hs hst h ih => exact f0 ms ms' ms'' hs hst h ih

/-! ## The write node over an arbitrary (fd, channel) pair -/

/-- The fd is open on channel `ch`, and `ch` is not stdin (which
`write_spec` rejects with -EBADF).  `fd` is stated already truncated
to 32 bits, as `check_syscall` hands it to `check_write`. -/
def fdchan (fd ch : word) (model : Model) : Prop :=
  fd_lookup (m_fds model) fd = some (FdEntry.FdChannel ch) ∧ w_is0 ch = false

theorem fd1chan_fdchan (model : Model) (H : fd1chan model) :
    fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model :=
  ⟨H, rfl⟩

theorem write_ch_check_n (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (fd ch : word) (buf : List byte) (n : Nat)
    (hfdc : fdchan fd ch model) (h32 : fd32 fd = fd) (_hno : bv_unsigned x8 = 64)
    (hg : ms_gpr ms 0 = fd)
    (hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (hcnt : buf_modeled buf) (hn1 : 1 ≤ n) (hn2 : n ≤ buf.length) :
    check_write (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
      (with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] [])) model
      = CheckOk model (List.map (WriteEv ch) (buf.take n)) := by
  obtain ⟨hfd, hch⟩ := hfdc
  have hrb : read_bytes_map (sys_input segs ms x8).in_mem (ms_gpr ms 1) (ms_gpr ms 2)
      = some buf := by
    rw [in_mem_sys_input, read_bytes_map_read_byte]
    exact hr
  have hlen := read_bytes_map_length _ _ _ _ hrb
  have hcr := word_unsigned_range (ms_gpr ms 2)
  have hcw : bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max := by
    unfold buf_modeled at hcnt
    omega
  have hmc := rw_range_in_range (ms_gpr ms 1) (ms_gpr ms 2) hcw
  have hc : w_is0 (ms_gpr ms 2) = false := w_is0_pos _ (by omega)
  have hne : buf.length ≠ 0 := by omega
  have hlf : ((buf.take n).length : Int) = (n : Int) := by
    rw [List.length_take]
    omega
  have hru : bv_unsigned (len_word (buf.take n)) = (n : Int) := by
    rw [len_word_unsigned (buf.take n) (by unfold two_pow_64 at hcr ⊢; omega)]
    exact hlf
  have hd1 : (1 : Int) ≤ (n : Int) := by omega
  have hd2 : (n : Int) ≤ (buf.length : Int) := by omega
  have hacc : access_ranges_eqb [(ms_gpr ms 1, n)] [(ms_gpr ms 1, n)] = true :=
    (access_ranges_eqb_eq _ _).2 rfl
  unfold check_write
  rw [hg, h32, hfd]
  simp only [hch, hmc, hc, write_source_of_rw _ _ _ hcw, readable_bytes_full _ _ _ _ hrb,
    beq_iff_eq, hne, with_copyins, hru, hd1, hd2, decide_true, Bool.and_self,
    Int.toNat_natCast, hacc, Bool.false_eq_true, ↓reduceIte]

theorem write_ch_ok_n (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (fd ch : word) (buf : List byte) (n : Nat)
    (hfdc : fdchan fd ch model) (h32 : fd32 fd = fd) (hno : bv_unsigned x8 = 64)
    (hg : ms_gpr ms 0 = fd)
    (hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (hcnt : buf_modeled buf) (hn1 : 1 ≤ n) (hn2 : n ≤ buf.length) :
    syscall_spec (sys_input segs ms x8) model
      (Ok (with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] [])) model
        (List.map (WriteEv ch) (buf.take n))) :=
  (syscall_spec_write segs ms x8 model _ hno).2
    (check_write_sound_ok _ _ _ _ _ _ _ _
      (write_ch_check_n segs ms x8 model fd ch buf n hfdc h32 hno hg hr hcnt hn1 hn2))

theorem write_ch_ok_inv (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (fd ch : word) (eff : SyscallEffect) (model' : Model)
    (evs : List event) (buf : List byte)
    (hfdc : fdchan fd ch model) (h32 : fd32 fd = fd) (hno : bv_unsigned x8 = 64)
    (hg : ms_gpr ms 0 = fd)
    (hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (hnb : 1 ≤ buf.length)
    (hspec : syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) :
    ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧
      eff = with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] []) ∧
      model' = model ∧ evs = List.map (WriteEv ch) (buf.take n) := by
  obtain ⟨hfd, hch⟩ := hfdc
  have hrb : read_bytes_map (sys_input segs ms x8).in_mem (ms_gpr ms 1) (ms_gpr ms 2)
      = some buf := by
    rw [in_mem_sys_input, read_bytes_map_read_byte]
    exact hr
  have hlen := read_bytes_map_length _ _ _ _ hrb
  have hck := check_write_complete_ok _ _ _ _ _ _ _ _
    ((syscall_spec_write segs ms x8 model _ hno).1 hspec)
  have hc : w_is0 (ms_gpr ms 2) = false := w_is0_pos _ (by omega)
  -- the source the transfer sees is the CLAMPED prefix of the range the
  -- call named -- `buf` itself for every count under `MAX_RW_COUNT`, and
  -- a prefix of it above, which the gate accepts at an in-range buffer
  have hcl := rw_count_clamp_range (ms_gpr ms 2)
  have hcpos : 1 ≤ (rw_count_clamp (ms_gpr ms 2)).toNat := by
    unfold rw_count_clamp MAX_RW_COUNT at *
    omega
  have hne : (buf.take (rw_count_clamp (ms_gpr ms 2)).toNat).length ≠ 0 := by
    rw [List.length_take]
    omega
  have hfl := List.length_take_le' (rw_count_clamp (ms_gpr ms 2)).toNat buf
  have hfc := List.length_take_le (rw_count_clamp (ms_gpr ms 2)).toNat buf
  unfold check_write at hck
  rw [hg, h32, hfd] at hck
  simp only [hch, hc, write_source_prefix _ _ _ _ hrb, beq_iff_eq, hne,
    Bool.false_eq_true, ↓reduceIte] at hck
  split at hck
  · cases hck
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons _ _ => cases hck
  | nil =>
  cases zs with
  | cons _ _ => cases hck
  | nil =>
  cases us with
  | cons _ _ => cases hck
  | nil =>
  cases cs with
  | cons _ _ => cases hck
  | nil =>
  dsimp only at hck
  split at hck
  · rename_i hgr
    split at hck
    · rename_i hreads
      cases hck
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hgr
      obtain ⟨hg1, hg2⟩ := hgr
      have hcp := (access_ranges_eqb_eq _ _).1 hreads
      subst hcp
      have hnc : (bv_unsigned ret).toNat ≤ (rw_count_clamp (ms_gpr ms 2)).toNat := by
        omega
      have hlw : len_word (buf.take (bv_unsigned ret).toNat) = ret :=
        len_word_firstn_ret ret buf ⟨by omega, by omega⟩
      refine ⟨(bv_unsigned ret).toNat, by omega, by omega, ?_, rfl, ?_⟩
      · rw [hlw]
        rfl
      · rw [List.take_take, Nat.min_eq_left hnc]
    · cases hck
  · cases hck

theorem write_ch_no_unmodeled (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (fd ch : word) (buf : List byte)
    (hfdc : fdchan fd ch model) (h32 : fd32 fd = fd) (hno : bv_unsigned x8 = 64)
    (hg : ms_gpr ms 0 = fd)
    (hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (hcnt : buf_modeled buf)
    -- Rocq's hypothesis, kept for fidelity.  It is not what keeps the spec
    -- modeled: a zero `count` reaches `Uaccess.access_ok_zero`, which answers
    -- 0 or -EFAULT and never `unmodeled`.  (Rocq's comment on this
    -- hypothesis calls a zero count unmodeled, pointing at
    -- `write1_no_unmodeled`'s, which says so "when the range verdict is
    -- unclear"; the channel arm of the current write spec makes it
    -- unmodeled in neither case.)
    (hnb : 1 ≤ buf.length) :
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled := by
  intro hspec
  obtain ⟨hfd, hch⟩ := hfdc
  have hrb : read_bytes_map (sys_input segs ms x8).in_mem (ms_gpr ms 1) (ms_gpr ms 2)
      = some buf := by
    rw [in_mem_sys_input, read_bytes_map_read_byte]
    exact hr
  have hlen := read_bytes_map_length _ _ _ _ hrb
  have hcw : bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max := by
    unfold buf_modeled at hcnt
    omega
  have hmc := rw_range_in_range (ms_gpr ms 1) (ms_gpr ms 2) hcw
  have hc : w_is0 (ms_gpr ms 2) = false := w_is0_pos _ (by omega)
  have hne : buf.length ≠ 0 := by omega
  have hck := check_write_complete_unmodeled _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []) _
    ((syscall_spec_write segs ms x8 model _ hno).1 hspec)
  unfold check_write at hck
  rw [hg, h32, hfd] at hck
  simp only [hch, hmc, hc, write_source_of_rw _ _ _ hcw, readable_bytes_full _ _ _ _ hrb,
    beq_iff_eq, hne, Bool.false_eq_true, ↓reduceIte] at hck
  repeat' split at hck
  all_goals cases hck

theorem sstep_write_ch_inv (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd)
    (ms : machine_state) (model : Model) (x8 : word) (buf : List byte)
    (evs : List event) (st : step_to)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = [])
    (hfdc : fdchan fd ch model) (hsvc : ms.ms_svc_pending = some x8)
    (hno : bv_unsigned x8 = 64) (hg : ms_gpr ms 0 = fd)
    (hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (hcnt : buf_modeled buf) (hnb : 1 ≤ buf.length)
    (hss : sstep segs (config.mkCfg ms model) evs st) :
    ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧ evs = List.map (WriteEv ch) (buf.take n) ∧
      st = SNext (config.mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model) := by
  cases hss with
  | sstep_instr _ _ _ _ _ hv _ => rw [hsvc] at hv; cases hv
  | sstep_instr_fault _ _ _ hv _ => rw [hsvc] at hv; cases hv
  | sstep_instr_unmodeled _ _ _ hv _ => rw [hsvc] at hv; cases hv
  | sstep_syscall _ _ x8' eff m' m'' evs' _ hv hspec _ hmat =>
    rw [hsvc] at hv
    cases hv
    obtain ⟨n, hn1, hn2, heff, hm, hevs⟩ :=
      write_ch_ok_inv segs ms x8 model fd ch eff m' _ buf hfdc Hfd32 hno hg hr hnb hspec
    subst heff hm hevs
    rw [materialize_model_accesses_no_lazy _ _ hlazy] at hmat
    cases hmat
    refine ⟨n, hn1, hn2, rfl, ?_⟩
    rw [apply_effect_copyins_no_write]
  | sstep_syscall_materialization_fault _ _ x8' eff m' evs' _ hv hspec _ hmat =>
    rw [hsvc] at hv
    cases hv
    obtain ⟨_, _, _, _, hm, _⟩ :=
      write_ch_ok_inv segs ms x8 model fd ch eff m' _ buf hfdc Hfd32 hno hg hr hnb hspec
    subst hm
    rw [materialize_model_accesses_no_lazy _ _ hlazy] at hmat
    cases hmat
  | sstep_exit _ _ x8' eff m' evs' code _ hv hspec hh' _ =>
    rw [hsvc] at hv
    cases hv
    obtain ⟨_, _, _, _, hm, _⟩ :=
      write_ch_ok_inv segs ms x8 model fd ch eff m' _ buf hfdc Hfd32 hno hg hr hnb hspec
    subst hm
    rw [hh] at hh'
    cases hh'
  | sstep_killed _ _ x8' eff m' evs' sig _ hv hspec hk =>
    -- the write arm hands back the model it was given, and a running model
    -- is not a killed one
    rw [hsvc] at hv
    cases hv
    obtain ⟨_, _, _, _, hm, _⟩ :=
      write_ch_ok_inv segs ms x8 model fd ch eff m' _ buf hfdc Hfd32 hno hg hr hnb hspec
    subst hm
    rw [m_killed_of_m_halted_none _ hh] at hk
    cases hk
  | sstep_syscall_unmodeled _ _ x8' _ hv hspec =>
    rw [hsvc] at hv
    cases hv
    exact absurd hspec
      (write_ch_no_unmodeled segs ms x8 model fd ch buf hfdc Hfd32 hno hg hr hcnt hnb)

/-! ## Additions for ticket E-proof-library-2c: `to_wexit` and the `msteps` bridges

Ported from the same Rocq file at the baseline the header names, with the
Rocq statements: the exit-after-writes relation `to_wexit`, `msteps_trans`
and `msteps_to_wexit`, which `Common/Hoare.lean`'s `triple_seq`,
`triple_seq_same` and `triple_wexit` use, and `to_wexit_ind`, which comes
along as Rocq's generated induction principle for `to_wexit` (stated as a
theorem, as `msteps_ind` is above).  Rocq's generated SProp eliminators
`to_wexit_sind` and `msteps_sind` have no twin (Lean has no SProp).
`to_wexit` is declared in Rocq's `Section WithSegs`, so the type takes
`segs` first, as `msteps` does.  Its constructors take `segs` implicitly,
as `msteps`'s do: Lean makes an inductive's parameters implicit in its
constructors, where Rocq's section-closed constructors take `segs` first
(Rocq's `CatSim.v` applies `sstep_instr segs ms model ms' model`;
`msteps_to_wexit` below applies `to_wexit.tw_step _ _ _ _ hsvc hstep …`).
Rocq's `firstn n buf` is `buf.take n`, and `is_exit_no` is
`ExitSim.is_exit_no` (the Rocq file imports `ExitSim`). -/

/-- The machine-deterministic straight line of writes then exit.  The write
node is RET-OBLIVIOUS: the continuation must hold for every length `n` from
1 to the whole buffer, not for one chosen delivery.  Rocq's comment, that
the environment may deliver any nonempty prefix, is not carried over:
`write_spec` on a channel delivers a prefix of at most
`rw_count_clamp count` bytes (`MAX_RW_COUNT` is `0x7ffff000`), shorter than
the whole buffer when the count is above that. -/
inductive to_wexit (segs : List Segment) : machine_state → List (List byte) → word → Prop
  | tw_exit : ∀ ms x8,
      ms.ms_svc_pending = some x8 →
      ExitSim.is_exit_no x8 →
      to_wexit segs ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
  | tw_write : ∀ ms x8 buf bufs code,
      ms.ms_svc_pending = some x8 →
      bv_unsigned x8 = 64 →
      ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
      1 ≤ buf.length →
      (∀ n, 1 ≤ n → n ≤ buf.length →
        to_wexit segs (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) bufs code) →
      to_wexit segs ms (buf :: bufs) code
  | tw_step : ∀ ms ms' bufs code,
      ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' →
      to_wexit segs ms' bufs code →
      to_wexit segs ms bufs code

/-- Rocq's generated induction principle for `to_wexit`.  Lean generates no
non-dependent `_ind`: `to_wexit.rec` takes a motive over the derivation, so
it is stated here with the Rocq statement, each recursive premise followed
by its hypothesis as Rocq orders them. -/
theorem to_wexit_ind (segs : List Segment)
    (P : machine_state → List (List byte) → word → Prop)
    (f : ∀ ms x8, ms.ms_svc_pending = some x8 → ExitSim.is_exit_no x8 →
      P ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)))
    (f0 : ∀ ms x8 buf bufs code, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 →
      ms_gpr ms 0 = Z_to_bv 64 1 → ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
      1 ≤ buf.length →
      (∀ n, 1 ≤ n → n ≤ buf.length →
        to_wexit segs (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) bufs code) →
      (∀ n, 1 ≤ n → n ≤ buf.length →
        P (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) bufs code) →
      P ms (buf :: bufs) code)
    (f1 : ∀ ms ms' bufs code, ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      to_wexit segs ms' bufs code → P ms' bufs code → P ms bufs code) :
    ∀ m l w, to_wexit segs m l w → P m l w := by
  intro m l w h
  induction h with
  | tw_exit ms x8 hs hx => exact f ms x8 hs hx
  | tw_write ms x8 buf bufs code hs hno hg hr hnb hcont ih =>
    exact f0 ms x8 buf bufs code hs hno hg hr hnb hcont ih
  | tw_step ms ms' bufs code hs hst h ih => exact f1 ms ms' bufs code hs hst h ih

theorem msteps_trans (segs : List Segment) (ms ms' ms'' : machine_state)
    (h1 : msteps segs ms ms') (h2 : msteps segs ms' ms'') : msteps segs ms ms'' := by
  induction h1 with
  | mst_refl => exact h2
  | mst_step _ _ _ hsvc hstep _ ih => exact msteps.mst_step _ _ _ hsvc hstep (ih h2)

theorem msteps_to_wexit (segs : List Segment) (ms ms' : machine_state)
    (bufs : List (List byte)) (code : word)
    (h : msteps segs ms ms') (hw : to_wexit segs ms' bufs code) :
    to_wexit segs ms bufs code := by
  induction h with
  | mst_refl => exact hw
  | mst_step _ _ _ hsvc hstep _ ih => exact to_wexit.tw_step _ _ _ _ hsvc hstep (ih hw)

end LinuxProcessSemantics.Common.CatSim

/-! ## Additions for E-proof-library-2a

Ported from `theories/Common/CatSim.v` with the Rocq statements, for
ticket E-proof-library-2a, and appended under the lead's ruling of
2026-09-29 on #1298's files: the declarations above are unchanged.  The
Rocq file was read at 7ba58b45f (`nightly/09-28-2026`), where it matches
the commit the header names byte for byte; 62d810d34 was the last commit
to change it.

`Common/AllocSim.lean` reaches these, directly or through the
`Common/WallSim.lean` additions: `bufs_modeled` and the full-delivery
event lists `wevents_ch` and `wevents`.  It also reaches the
write-then-exit node `to_wexit` that `WallSim.to_wallexit` ends in, which
ticket E-proof-library-2c's section above declares, with its induction
principle `to_wexit_ind`.

Spellings, beyond the header's: Rocq `Forall P l` is `∀ b ∈ l, P b`
(`bufs_modeled`). -/

namespace LinuxProcessSemantics.Common.CatSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run

/-- A whole run's worth of buffers is inside the transfer size
`buf_modeled` states. -/
def bufs_modeled (bufs : List (List byte)) : Prop :=
  ∀ b ∈ bufs, buf_modeled b

/-- The full-delivery trace of a run's writes on channel `ch`: one
`WriteEv ch` per byte of the buffers, in order. -/
def wevents_ch (ch : word) (bufs : List (List byte)) : List event :=
  match bufs with
  | [] => []
  | buf :: rest => List.map (WriteEv ch) buf ++ wevents_ch ch rest

/-- The channel-1 instance of `wevents_ch`, which `wevents_ch_fd1` (in
`Common/WallSim.lean`) equates to it. -/
def wevents (bufs : List (List byte)) : List event :=
  match bufs with
  | [] => []
  | buf :: rest => List.map (WriteEv (Z_to_bv 64 1)) buf ++ wevents rest

end LinuxProcessSemantics.Common.CatSim

/-! ## Additions for E-proof-library-2a (MmapSim)

Ported from `theories/Common/CatSim.v` with the Rocq statements, for
ticket E-proof-library-2a, and appended under the lead's ruling of
2026-09-29 on #1298's files: the declarations above are unchanged.  The
Rocq file was read at 7ba58b45f (`nightly/09-28-2026`).

`Common/MmapSim.lean` reaches the fd-1 write node `write1_ok_n` and its
inversion `sstep_write_inv`.  `Print All Dependencies` of the
`strong_universal` of alloc_join, arena_tee, brk_rev, mmap_upper,
modprint and oob_read names the declarations below.

Spellings, beyond the header's: `sstep_write_next_inv` and
`sstep_write_inv` take Rocq's Section variable `segs` as their first
argument. -/

namespace LinuxProcessSemantics.Common.CatSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite

/-- The channel-write spec facts at fd 1.  Rocq proves this by unfolding
`check_write`; here it is `write_ch_check_n` at `fd = ch = 1`. -/
theorem write1_check_n (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (buf : List byte) (n : Nat)
    (Hfd : fd1chan model) (Hno : bv_unsigned x8 = 64) (Hg : ms_gpr ms 0 = Z_to_bv 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hcnt : buf_modeled buf) (Hn1 : 1 ≤ n) (Hn2 : n ≤ buf.length) :
    check_write (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
      (with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] [])) model
      = CheckOk model (List.map (WriteEv (Z_to_bv 64 1)) (buf.take n)) :=
  write_ch_check_n segs ms x8 model _ _ buf n (fd1chan_fdchan model Hfd)
    (fd32_id _ (by decide)) Hno Hg Hr Hcnt Hn1 Hn2

/-- The `n`-byte delivery is admissible, for `1 ≤ n ≤ length buf`. -/
theorem write1_ok_n (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (buf : List byte) (n : Nat)
    (Hfd : fd1chan model) (Hno : bv_unsigned x8 = 64) (Hg : ms_gpr ms 0 = Z_to_bv 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hcnt : buf_modeled buf) (Hn1 : 1 ≤ n) (Hn2 : n ≤ buf.length) :
    syscall_spec (sys_input segs ms x8) model
      (Ok (with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] [])) model
        (List.map (WriteEv (Z_to_bv 64 1)) (buf.take n))) :=
  (syscall_spec_write segs ms x8 model _ Hno).2
    (check_write_sound_ok _ _ _ _ _ _ _ _
      (write1_check_n segs ms x8 model buf n Hfd Hno Hg Hr Hcnt Hn1 Hn2))

/-- An admissible write-to-fd-1 outcome delivers a nonempty prefix.  Rocq
proves this by unfolding `check_write`; here it is `write_ch_ok_inv` at
`fd = ch = 1`. -/
theorem write1_ok_inv (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (eff : SyscallEffect) (model' : Model) (evs : List event) (buf : List byte)
    (Hfd : fd1chan model) (Hno : bv_unsigned x8 = 64) (Hg : ms_gpr ms 0 = Z_to_bv 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hnb : 1 ≤ buf.length)
    (Hspec : syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) :
    ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧
      eff = with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] []) ∧
      model' = model ∧ evs = List.map (WriteEv (Z_to_bv 64 1)) (buf.take n) :=
  write_ch_ok_inv segs ms x8 model _ _ eff model' evs buf (fd1chan_fdchan model Hfd)
    (fd32_id _ (by decide)) Hno Hg Hr Hnb Hspec

/-- Rocq proves this by unfolding `check_write`; here it is
`write_ch_no_unmodeled` at `fd = ch = 1`, whose comment on the `Hnb`
hypothesis applies here too. -/
theorem write1_no_unmodeled (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (buf : List byte)
    (Hfd : fd1chan model) (Hno : bv_unsigned x8 = 64) (Hg : ms_gpr ms 0 = Z_to_bv 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hcnt : buf_modeled buf) (Hnb : 1 ≤ buf.length) :
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled :=
  write_ch_no_unmodeled segs ms x8 model _ _ buf (fd1chan_fdchan model Hfd)
    (fd32_id _ (by decide)) Hno Hg Hr Hcnt Hnb

/-- The step that happened, inverted.  Being handed `SNext` already
excludes the error transition, so no `buf_modeled` hypothesis is needed;
`sstep_write_inv` below, which rules the error transition out, takes
one. -/
theorem sstep_write_next_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (buf : List byte) (evs : List event) (c' : config)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 64)
    (Hg : ms_gpr ms 0 = Z_to_bv 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hnb : 1 ≤ buf.length)
    (Hss : sstep segs (config.mkCfg ms model) evs (SNext c')) :
    ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧ evs = List.map (WriteEv (Z_to_bv 64 1)) (buf.take n) ∧
      c' = config.mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model := by
  cases Hss with
  | sstep_instr _ _ _ _ _ hv _ => rw [Hsvc] at hv; cases hv
  | sstep_syscall _ _ x8' eff m' m'' evs' _ hv hspec _ hmat =>
    rw [Hsvc] at hv
    cases hv
    obtain ⟨n, hn1, hn2, heff, hm, hevs⟩ :=
      write1_ok_inv segs ms x8 model eff m' _ buf Hfd Hno Hg Hr Hnb hspec
    subst heff hm hevs
    rw [materialize_model_accesses_no_lazy _ _ Hlazy] at hmat
    cases hmat
    refine ⟨n, hn1, hn2, rfl, ?_⟩
    rw [apply_effect_copyins_no_write]
  | sstep_exit _ _ x8' eff m' evs' code _ hv hspec hh' _ =>
    -- the write arm hands back the model it was given, which is not halted
    rw [Hsvc] at hv
    cases hv
    obtain ⟨_, _, _, _, hm, _⟩ :=
      write1_ok_inv segs ms x8 model eff m' _ buf Hfd Hno Hg Hr Hnb hspec
    subst hm
    rw [Hh] at hh'
    cases hh'
  | sstep_killed _ _ x8' eff m' evs' sig _ hv hspec hk =>
    -- nor killed, through `State.m_killed_of_m_halted_none`
    rw [Hsvc] at hv
    cases hv
    obtain ⟨_, _, _, _, hm, _⟩ :=
      write1_ok_inv segs ms x8 model eff m' _ buf Hfd Hno Hg Hr Hnb hspec
    subst hm
    rw [m_killed_of_m_halted_none _ Hh] at hk
    cases hk

/-- Rocq proves this by inverting the step; here it is `sstep_write_ch_inv`
at `fd = ch = 1`. -/
theorem sstep_write_inv (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (buf : List byte) (evs : List event) (st : step_to)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 64)
    (Hg : ms_gpr ms 0 = Z_to_bv 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hcnt : buf_modeled buf) (Hnb : 1 ≤ buf.length)
    (Hss : sstep segs (config.mkCfg ms model) evs st) :
    ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧ evs = List.map (WriteEv (Z_to_bv 64 1)) (buf.take n) ∧
      st = SNext (config.mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model) :=
  sstep_write_ch_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) (fd32_id _ (by decide)) ms model x8 buf
    evs st Hh Hlazy (fd1chan_fdchan model Hfd) Hsvc Hno Hg Hr Hcnt Hnb Hss

end LinuxProcessSemantics.Common.CatSim

/-! ## Additions for ticket E-conditional_bug_ns

Ported from `theories/Common/CatSim.v` with the Rocq statements. The
Rocq file was read at f44244ad6b8041aa83053d9ca91e090037ed743b, where it
matches the header's commit byte for byte.
`theories/Examples/conditional_bug_ns/Proof.v` glues its
no-output arms with `cat_omni_strong_equiv_te` and its 'h' arm with
`WallSim.wall_omni_strong_equiv`.

Section variables become explicit leading arguments; `to_wexit_ch` takes
`segs fd`, since Rocq drops the unused `ch`. Constructors take those
parameters implicitly. Rocq `firstn` is `List.take`, and `Forall` is
membership-indexed universal quantification, as in `bufs_modeled` above.
The existing write-step helpers are reused; no declaration above needs to
move for Lean's declaration order. -/

namespace LinuxProcessSemantics.Common.CatSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Common.ExitSim

/-- A single modeled buffer forms a modeled buffer list. -/
theorem bufs_modeled_single (b : List byte) (H : buf_modeled b) : bufs_modeled [b] := by
  intro b' hb
  have heq := List.mem_singleton.mp hb
  subst b'
  exact H

/-- A delivery choice selects a nonempty prefix of each buffer. -/
inductive wpick (ch : word) : List (List byte) → List event → Prop
  | wp_nil : wpick ch [] []
  | wp_cons : ∀ buf bufs n tr,
      1 ≤ n → n ≤ buf.length → wpick ch bufs tr →
      wpick ch (buf :: bufs) (List.map (WriteEv ch) (buf.take n) ++ tr)

/-- The completed trace contains a delivery choice followed by the stated exit. -/
def wexit_post (bufs : List (List byte)) (code : word)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) : post :=
  fun tr o =>
    (∃ full, wpick (Z_to_bv 64 1) bufs full ∧ tr = full ++ [ExitEv code fs]) ∧
    exits_with code tr o

/-- A modeled write-then-exit derivation satisfies its delivery-choice postcondition. -/
theorem to_wexit_exec (segs : List Segment) (ms : machine_state)
    (bufs : List (List byte)) (code : word) (Hte : to_wexit segs ms bufs code)
    (model : Model) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (Hbm : bufs_modeled bufs) :
    exec segs (config.mkCfg ms model) (wexit_post bufs code (m_fs model)) := by
  induction Hte generalizing model with
  | tw_exit ms x8 Hsvc Hx8 =>
    apply exec_step_only segs _ _
      [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      (config.mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))
    · exact sstep.sstep_exit ms model x8 _ _ [] _ Hh Hsvc
        (exit_dispatch_ok _ model Hx8) rfl rfl
    · intro evs st Hss
      exact sstep_exit_inv _ _ _ _ _ _ Hh Hsvc Hx8 Hss
    · apply exec.exec_halt
      · simp only [m_halted_with_halted, ne_eq, reduceCtorEq, not_false_eq_true]
      · exact ⟨⟨[], wpick.wp_nil, rfl⟩,
          m_halted_with_halted _ _, m_killed_with_halted _ _⟩
  | tw_write ms x8 buf bufs code Hsvc Hno Hg Hr Hnb _ IH =>
    have Hb : buf_modeled buf := Hbm buf List.mem_cons_self
    have Hbs : bufs_modeled bufs := fun b hb => Hbm b (List.mem_cons_of_mem _ hb)
    refine exec.exec_step _ _ Hh ?_ ?_ ?_
    · exact ⟨_, _, sstep.sstep_syscall ms model x8
        (with_copyins [(ms_gpr ms 1, buf.length)]
          (mkEffect (len_word (buf.take buf.length)) [] [])) model model
        (List.map (WriteEv (Z_to_bv 64 1)) (buf.take buf.length)) Hh Hsvc
        (write1_ok_n segs ms x8 model buf buf.length Hfd Hno Hg Hr Hb Hnb (Nat.le_refl _))
        Hh (materialize_model_accesses_no_lazy model _ Hlazy)⟩
    · intro evs Hss
      obtain ⟨_, _, _, _, Habs⟩ :=
        sstep_write_inv segs ms model x8 buf evs SError Hh Hlazy Hfd Hsvc Hno Hg Hr Hb Hnb Hss
      cases Habs
    · intro evs c' Hss
      obtain ⟨n, Hn1, Hn2, Hevs, Hc⟩ :=
        sstep_write_inv segs ms model x8 buf evs (SNext c')
          Hh Hlazy Hfd Hsvc Hno Hg Hr Hb Hnb Hss
      subst evs
      cases Hc
      refine exec_conseq _ _ _ _ (IH n Hn1 Hn2 model Hh Hlazy Hfd Hbs) ?_
      rintro tr o ⟨⟨full, Hpick, rfl⟩, Hx⟩
      exact ⟨⟨_, wpick.wp_cons buf bufs n full Hn1 Hn2 Hpick,
        (List.append_assoc _ _ _).symm⟩, Hx⟩
  | tw_step ms ms' _ _ Hsvc Hstep _ IH =>
    apply exec_step_only segs _ _ [] (config.mkCfg ms' model)
    · exact sstep.sstep_instr ms model ms' model Hh Hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])
    · intro evs st Hss
      exact sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss
    · exact IH model Hh Hlazy Hfd Hbm

/-- A specified delivery choice is realized by a finite run through the exit. -/
theorem to_wexit_star_admits (segs : List Segment) (ms : machine_state)
    (bufs : List (List byte)) (code : word) (Hte : to_wexit segs ms bufs code)
    (model : Model) (full : List event)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (Hbm : bufs_modeled bufs)
    (Hpick : wpick (Z_to_bv 64 1) bufs full) :
    ∃ c, star segs (config.mkCfg ms model) (full ++ [ExitEv code (m_fs model)]) c := by
  induction Hte generalizing model full with
  | tw_exit ms x8 Hsvc Hx8 =>
    cases Hpick
    exact ⟨_, star_one _ _ _ _ (sstep.sstep_exit ms model x8 _
      (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) [] _ Hh Hsvc
      (exit_dispatch_ok _ model Hx8) rfl rfl)⟩
  | tw_write ms x8 buf bufs code Hsvc Hno Hg Hr _ _ IH =>
    have Hb : buf_modeled buf := Hbm buf List.mem_cons_self
    have Hbs : bufs_modeled bufs := fun b hb => Hbm b (List.mem_cons_of_mem _ hb)
    cases Hpick with
    | wp_cons _ _ n tr Hn1 Hn2 Hpick =>
      obtain ⟨c, Hstar⟩ := IH n Hn1 Hn2 model tr Hh Hlazy Hfd Hbs Hpick
      refine ⟨c, ?_⟩
      rw [List.append_assoc]
      refine star.star_step _ _ _ _ _ ?_ Hstar
      exact sstep.sstep_syscall ms model x8
        (with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] []))
        model model (List.map (WriteEv (Z_to_bv 64 1)) (buf.take n)) Hh Hsvc
        (write1_ok_n segs ms x8 model buf n Hfd Hno Hg Hr Hb Hn1 Hn2)
        Hh (materialize_model_accesses_no_lazy model _ Hlazy)
  | tw_step ms ms' _ _ Hsvc Hstep _ IH =>
    obtain ⟨c, Hstar⟩ := IH model full Hh Hlazy Hfd Hbm Hpick
    exact ⟨c, star.star_step _ [] _ _ _
      (sstep.sstep_instr ms model ms' model Hh Hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])) Hstar⟩

/-- A finite run's trace is a prefix of a delivery choice followed by the exit. -/
theorem to_wexit_star_only (segs : List Segment) (ms : machine_state)
    (bufs : List (List byte)) (code : word) (Hte : to_wexit segs ms bufs code)
    (model : Model) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (Hbm : bufs_modeled bufs)
    (tr : List event) (c : config) (Hstar : star segs (config.mkCfg ms model) tr c) :
    ∃ full, wpick (Z_to_bv 64 1) bufs full ∧
      is_prefix tr (full ++ [ExitEv code (m_fs model)]) := by
  obtain ⟨tr', o, _, ⟨full, Hpick, Heq⟩, _⟩ := exec_realizes _ _ _
    (exec_star _ _ _ _ _ (to_wexit_exec segs ms bufs code Hte model Hh Hlazy Hfd Hbm) Hstar)
  refine ⟨full, Hpick, ?_⟩
  rw [← Heq]
  exact is_prefix_app tr tr'

/-- A modeled write-then-exit derivation excludes the explicit error transition. -/
theorem to_wexit_no_error (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model)
    (Hte : to_wexit segs ms bufs code) (Hbm : bufs_modeled bufs) :
    ¬ reaches_error segs (config.mkCfg ms model) := by
  apply exec_no_error
  exact exec_conseq _ _ _ _ (to_wexit_exec segs ms bufs code Hte model Hh Hlazy Hfd Hbm)
    (fun tr o h => exits_with_never_errors _ tr o h.2)

/-- The run-level omni judgment of a write-then-exit binary. -/
theorem cat_omni_run_te (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bufs : List (List byte)) (code : word)
    (Hte : to_wexit segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      bufs code) (Hbm : bufs_modeled bufs) :
    omni_run (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp
      (wexit_post bufs code inp.in_fs) :=
  to_wexit_exec segs _ bufs code Hte
    (init_model (segments_reserved segs) brk0 mb sp lim inp) rfl rfl rfl Hbm

/-- Observable traces are precisely prefixes of the completed delivery choices. -/
theorem cat_obs_iff_te (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bufs : List (List byte)) (code : word)
    (Hte : to_wexit segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      bufs code) (Hbm : bufs_modeled bufs) (tr : List event) :
    obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
      ∃ full, wpick (Z_to_bv 64 1) bufs full ∧ is_prefix tr (full ++ [ExitEv code inp.in_fs]) := by
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    obtain ⟨full, Hw, Hpref⟩ := to_wexit_star_only segs _ bufs code Hte
      (init_model (segments_reserved segs) brk0 mb sp lim inp) rfl rfl rfl Hbm tr' c Hstar
    exact ⟨full, Hw, is_prefix_trans _ _ _ Hp Hpref⟩
  · rintro ⟨full, Hw, Hp⟩
    obtain ⟨c, Hstar⟩ := to_wexit_star_admits segs _ bufs code Hte
      (init_model (segments_reserved segs) brk0 mb sp lim inp) full rfl rfl rfl Hbm Hw
    exact ⟨full ++ [ExitEv code inp.in_fs], c, Hstar, Hp⟩

/-- The initialized write-then-exit run does not reach an explicit error. -/
theorem cat_no_error_run_te (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bufs : List (List byte)) (code : word)
    (Hte : to_wexit segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      bufs code) (Hbm : bufs_modeled bufs) :
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  apply exec_no_error
  exact exec_conseq _ _ _ _ (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm)
    (fun tr o h => exits_with_never_errors _ tr o h.2)

/-- Equal buffers and exit code give omni strong equivalence at the role budgets. -/
theorem cat_omni_strong_equiv_te (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo) (asp abrk amb : word)
    (arnd : EntryDraw) (bufs : List (List byte)) (code : word) (inp : ProcInput)
    (Hsource : to_wexit source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      bufs code)
    (Htarget : to_wexit target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      bufs code) (Hbm : bufs_modeled bufs) :
    omni_strong_equiv (Image.mkImage source_segs rpc rph) (Image.mkImage target_segs apc aph)
      (ExecEntry.mkEntry rsp rbrk rmb rrnd) (ExecEntry.mkEntry asp abrk amb arnd) inp := by
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · refine coexec_conseq _ _ _ _
      (exec_coexec _ _ _ (cat_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd
        source_alloc_limit inp bufs code Hsource Hbm)) ?_
    intro tr o h
    exact never_errors_covered _ _ _ (exits_with_never_errors _ tr o h.2)
  · refine (trace_equiv_iff_omni _ _ _ _ _ _ _).1 ?_
    intro tr
    exact (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp
      bufs code Hsource Hbm tr).trans
      (cat_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp
        bufs code Htarget Hbm tr).symm
  · exact (bh_errors_iff (Image.mkImage target_segs apc aph) target_alloc_limit
      (ExecEntry.mkEntry asp abrk amb arnd) inp).1
      (cat_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp
        bufs code Htarget Hbm)

/-- Equal buffers and exit code give modeledness and equivalence at the supplied budgets. -/
theorem cat_strong_equiv_te (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo) (asp abrk amb : word)
    (arnd : EntryDraw) (alim : Int) (bufs : List (List byte)) (code : word) (inp : ProcInput)
    (Hsource : to_wexit source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      bufs code)
    (Htarget : to_wexit target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      bufs code) (Hbm : bufs_modeled bufs) :
    modeled (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp) ∧
    equiv (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp)
      (run (Image.mkImage target_segs apc aph) alim (ExecEntry.mkEntry asp abrk amb arnd) inp) := by
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · exact no_error_no_unmodeled _ _
      (cat_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm)
  · intro tr
    exact (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm tr).trans
      (cat_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bufs code Htarget Hbm tr).symm
  · exact cat_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bufs code Htarget Hbm

/-- The fd-parametric write-then-exit relation, with a return-oblivious write node. -/
inductive to_wexit_ch (segs : List Segment) (fd : word) :
    machine_state → List (List byte) → word → Prop
  | twc_exit : ∀ ms x8,
      ms.ms_svc_pending = some x8 → is_exit_no x8 →
      to_wexit_ch segs fd ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
  | twc_write : ∀ ms x8 buf bufs code,
      ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 → ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → 1 ≤ buf.length →
      (∀ n, 1 ≤ n → n ≤ buf.length →
        to_wexit_ch segs fd (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) bufs code) →
      to_wexit_ch segs fd ms (buf :: bufs) code
  | twc_step : ∀ ms ms' bufs code,
      ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      to_wexit_ch segs fd ms' bufs code → to_wexit_ch segs fd ms bufs code

/-- The fd-1 derivation embeds into the fd-parametric relation at fd 1. -/
theorem to_wexit_ch_1 (segs : List Segment) (ms : machine_state)
    (bufs : List (List byte)) (code : word) (H : to_wexit segs ms bufs code) :
    to_wexit_ch segs (Z_to_bv 64 1) ms bufs code := by
  induction H with
  | tw_exit ms x8 Hsvc Hx8 => exact to_wexit_ch.twc_exit ms x8 Hsvc Hx8
  | tw_write ms x8 buf bufs code Hsvc Hno Hg Hr Hnb _ IH =>
    exact to_wexit_ch.twc_write ms x8 buf bufs code Hsvc Hno Hg Hr Hnb IH
  | tw_step ms ms' bufs code Hsvc Hstep _ IH =>
    exact to_wexit_ch.twc_step ms ms' bufs code Hsvc Hstep IH

end LinuxProcessSemantics.Common.CatSim

/-! ## Additions for ticket E-conditional_bug_ns, second batch

Ported from `theories/Common/CatSim.v` with the Rocq statements; the Rocq
file was read at f44244ad6b8041aa83053d9ca91e090037ed743b. Other examples'
proofs reach `init_model_fd1chan`: `brk_rev_ns` and `arena_tee_ns`. -/

namespace LinuxProcessSemantics.Common.CatSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State

/-- The initial model resolves fd 1 to channel 1. -/
theorem init_model_fd1chan (reserved : List (word × word)) (brk0 mb sp : word)
    (lim : Int) (inp : ProcInput) :
    fd1chan (init_model reserved brk0 mb sp lim inp) := by
  rfl

end LinuxProcessSemantics.Common.CatSim
