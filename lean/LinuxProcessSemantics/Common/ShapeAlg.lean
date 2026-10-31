import LinuxProcessSemantics.Common.MmapSim
import LinuxProcessSemantics.Common.AllocSim2

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b
unported: t_writes_ch_pick_exit_iff -- the channel-parametric trace characterization needs CatSim.wpick_wevents, which has no Lean twin; cat_omni_strong_equiv_alg does not reach it
unported: t_writes_pick_exit_iff -- the channel-1 trace characterization is proved from t_writes_ch_pick_exit_iff, which is unported; cat_omni_strong_equiv_alg does not reach it
unported: mmap_strong_equiv_alg -- strong equivalence of two MmapSim.tmw derivations realizing the same binary shape; cat_omni_strong_equiv_alg does not reach it
unported: mmap_omni_strong_equiv_alg -- omni strong equivalence of two MmapSim.tmw derivations at the two role budgets; cat_omni_strong_equiv_alg does not reach it
unported: rz_alloc_writes -- an mmap prologue composed with a CatSim failure tail and a MmapSim.twm success tail; cat_omni_strong_equiv_alg does not reach it
unported: cat_strong_equiv_alg_via_ch -- the fd-1 instance of the channel-parametric cat strong-equivalence theorem; cat_omni_strong_equiv_alg does not reach it
unported: alloc_mmap_strong_equiv_alg -- strong equivalence between an AllocSim brk source and a MmapSim mmap target; cat_omni_strong_equiv_alg does not reach it
unported: alloc_mmap_omni_strong_equiv_alg -- omni strong equivalence between an AllocSim brk source and a MmapSim mmap target; cat_omni_strong_equiv_alg does not reach it
unported: cat_realizes_ch -- CatSim's to_wexit_ch bridge to the channel-parametric write-list shape; cat_omni_strong_equiv_alg does not reach it
unported: cat_ch_strong_equiv_alg -- strong equivalence for fd/channel-parametric cat derivations; cat_omni_strong_equiv_alg does not reach it
unported: cat_ch_omni_strong_equiv_alg -- omni strong equivalence for fd/channel-parametric cat derivations; cat_omni_strong_equiv_alg does not reach it
-/

/-! # Common.ShapeAlg — compositional trace shapes and realization nodes

This file is PROOF-SIDE, not part of the trusted specification.

An image-independent proof library: shapes denote finite trace-prefix sets,
and `realizes` connects their composition to exact indexed step families.
The generic observation and no-error theorems yield the cat equivalences,
including `cat_omni_strong_equiv_alg` used by modprint_ns.

Rocq `Z` is `Int`, `Forall P l` is `∀ x ∈ l, P x`, and section variables
are explicit leading arguments. Index types use Lean `Type` (universe zero),
as do configurations and events. Realization lives in `Prop`; Lean has no
Rocq `SProp` eliminator. The generated Lean recursor supplies induction.
-/

namespace LinuxProcessSemantics.Common.ShapeAlg

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.WallSim

theorem is_prefix_app_r {A : Type} (l m a : List A) (H : is_prefix a l) :
    is_prefix a (l ++ m) := is_prefix_trans _ _ _ H (is_prefix_app l m)

theorem is_prefix_app_split {A : Type} (l a b : List A) (H : is_prefix b (l ++ a)) :
    is_prefix b l ∨ ∃ b', b = l ++ b' ∧ is_prefix b' a := by
  induction l generalizing b with
  | nil => exact Or.inr ⟨b, rfl, H⟩
  | cons x l IH =>
    cases b with
    | nil => exact Or.inl (is_prefix_nil _)
    | cons y b =>
      obtain ⟨rfl, H⟩ := H
      rcases IH b H with Hp | ⟨b', rfl, Hp⟩
      · exact Or.inl ⟨rfl, Hp⟩
      · exact Or.inr ⟨b', rfl, Hp⟩

theorem is_prefix_nil_r {A : Type} (a : List A) (H : is_prefix a []) : a = [] := by
  cases a with
  | nil => rfl
  | cons _ _ => exact False.elim H

/-- A shape: realized shapes are nonempty and prefix-closed. -/
def TSet := List event → Prop

def t_eq (T T' : TSet) : Prop := ∀ tr, T tr ↔ T' tr

theorem t_eq_refl (T : TSet) : t_eq T T := fun _ => Iff.rfl
theorem t_eq_sym (T T' : TSet) (H : t_eq T T') : t_eq T' T := fun tr => (H tr).symm
theorem t_eq_trans (T1 T2 T3 : TSet) (H : t_eq T1 T2) (H' : t_eq T2 T3) :
    t_eq T1 T3 := fun tr => (H tr).trans (H' tr)

/-- The terminated shape contains only the empty trace. -/
def t_nil : TSet := fun tr => tr = []
/-- Emit a block and continue. The prefix disjunct includes observations
part-way through the block. -/
def t_emit (evs : List event) (T : TSet) : TSet :=
  fun tr => is_prefix tr evs ∨ ∃ tr', tr = evs ++ tr' ∧ T tr'
/-- Indexed nondeterministic choice. -/
def t_alt {I : Type} (f : I → TSet) : TSet := fun tr => ∃ i, f i tr
/-- Binary choice. -/
def t_alt2 (A B : TSet) : TSet := fun tr => A tr ∨ B tr
/-- Terminating leaf with exit code and final file system. -/
def t_exit (code : word) (fs : Fs.Fs) : TSet := t_emit [ExitEv code fs] t_nil
/-- Resolutions of a channel write: nonempty delivered prefixes. -/
def wr_index (buf : List byte) : Type := {n : Nat // 1 ≤ n ∧ n ≤ buf.length}
def wr_full (buf : List byte) (Hnb : 1 ≤ buf.length) : wr_index buf :=
  ⟨buf.length, Hnb, Nat.le_refl _⟩
/-- One channel write, choosing a nonempty prefix before continuing. -/
def t_write_ch (ch : word) (buf : List byte) (T : TSet) : TSet :=
  t_alt (fun i : wr_index buf => t_emit ((buf.take i.val).map (WriteEv ch)) T)
/-- A list of channel-1 writes, then the continuation. -/
def t_writes_pick (bufs : List (List byte)) (T : TSet) : TSet :=
  bufs.foldr (t_write_ch (Z_to_bv 64 1)) T

/-- An empty emission preserves any shape containing the empty trace. -/
theorem t_emit_nil_eq (T : TSet) (H0 : T []) : t_eq (t_emit [] T) T := by
  intro tr
  constructor
  · rintro (Hp | ⟨tr', rfl, HT⟩)
    · obtain rfl := is_prefix_nil_r tr Hp
      exact H0
    · exact HT
  · intro HT
    exact Or.inr ⟨tr, rfl, HT⟩

theorem t_writes_pick_nil (T : TSet) : t_writes_pick [] T = T := rfl
theorem t_writes_pick_cons (buf : List byte) (bufs : List (List byte)) (T : TSet) :
    t_writes_pick (buf :: bufs) T = t_write_ch (Z_to_bv 64 1) buf (t_writes_pick bufs T) := rfl

/-- Full-delivery writes, as produced by a retry loop irrespective of chunking. -/
def t_writes_ch (ch : word) (bufs : List (List byte)) (T : TSet) : TSet :=
  bufs.foldr (fun buf acc => t_emit (buf.map (WriteEv ch)) acc) T
def t_writes (bufs : List (List byte)) (T : TSet) : TSet :=
  t_writes_ch (Z_to_bv 64 1) bufs T

theorem t_writes_nil (T : TSet) : t_writes [] T = T := rfl
theorem t_writes_cons (buf : List byte) (bufs : List (List byte)) (T : TSet) :
    t_writes (buf :: bufs) T = t_emit (buf.map (WriteEv (Z_to_bv 64 1))) (t_writes bufs T) := rfl
theorem t_writes_ch_cons (ch : word) (buf : List byte) (bufs : List (List byte)) (T : TSet) :
    t_writes_ch ch (buf :: bufs) T = t_emit (buf.map (WriteEv ch)) (t_writes_ch ch bufs T) := rfl

/-- Every emit-chain shape contains the empty trace. -/
theorem t_emit_has_nil (e : List event) (T : TSet) : t_emit e T [] := Or.inl (is_prefix_nil _)
theorem t_writes_ch_exit_has_nil (ch : word) (bufs : List (List byte)) (code : word) (fs : Fs.Fs) :
    t_writes_ch ch bufs (t_exit code fs) [] := by
  cases bufs <;> exact t_emit_has_nil _ _

/-- Bridge to CatSim's prefixes of writes followed by the exit event. -/
theorem t_writes_ch_exit_iff (ch : word) (bufs : List (List byte)) (code : word) (fs : Fs.Fs)
    (tr : List event) :
    t_writes_ch ch bufs (t_exit code fs) tr ↔ is_prefix tr (wevents_ch ch bufs ++ [ExitEv code fs]) := by
  induction bufs generalizing tr with
  | nil =>
    change t_emit [ExitEv code fs] t_nil tr ↔ is_prefix tr [ExitEv code fs]
    constructor
    · rintro (H | ⟨tr', rfl, rfl⟩)
      · exact H
      · rw [List.append_nil]
        exact is_prefix_refl _
    · exact Or.inl
  | cons buf bufs IH =>
    change t_emit (buf.map (WriteEv ch)) (t_writes_ch ch bufs (t_exit code fs)) tr ↔ _
    change _ ↔ is_prefix tr ((buf.map (WriteEv ch) ++ wevents_ch ch bufs) ++ [ExitEv code fs])
    rw [List.append_assoc]
    constructor
    · rintro (H | ⟨tr', rfl, H⟩)
      · exact is_prefix_app_r _ _ _ H
      · exact is_prefix_app_mono _ _ _ ((IH tr').1 H)
    · intro H
      rcases is_prefix_app_split (buf.map (WriteEv ch)) (wevents_ch ch bufs ++ [ExitEv code fs]) tr H with Hpre | ⟨tr', Heq, Htail⟩
      · exact Or.inl Hpre
      · exact Or.inr ⟨tr', Heq, (IH tr').2 Htail⟩

theorem t_writes_exit_iff (bufs : List (List byte)) (code : word) (fs : Fs.Fs) (tr : List event) :
    t_writes bufs (t_exit code fs) tr ↔ is_prefix tr (wevents bufs ++ [ExitEv code fs]) := by
  unfold t_writes
  rw [t_writes_ch_exit_iff, wevents_ch_fd1]

/-- A retry-loop write collapses to one full-buffer emission: all delivery
alternatives followed by their remainders denote the same trace set. -/
theorem t_alt_wall (ch : word) (rest : List byte) (T : TSet)
    (_HT : T []) (Hnb : 1 ≤ rest.length) :
    t_eq (t_alt (fun i : wr_index rest =>
      t_emit ((rest.take i.val).map (WriteEv ch))
        (t_emit ((rest.drop i.val).map (WriteEv ch)) T)))
      (t_emit (rest.map (WriteEv ch)) T) := by
  intro tr
  have Hsplit (n : Nat) : rest.map (WriteEv ch) =
      (rest.take n).map (WriteEv ch) ++ (rest.drop n).map (WriteEv ch) := by
    rw [← List.map_append, List.take_append_drop]
  constructor
  · rintro ⟨⟨n, _, _⟩, Hp | ⟨tr1, rfl, Hi⟩⟩
    · exact Or.inl (is_prefix_trans _ _ _ Hp (by rw [Hsplit n]; exact is_prefix_app _ _))
    · rcases Hi with Hp | ⟨tr2, rfl, Ht⟩
      · exact Or.inl (by rw [Hsplit n]; exact is_prefix_app_mono _ _ _ Hp)
      · refine Or.inr ⟨tr2, ?_, Ht⟩
        rw [Hsplit n, List.append_assoc]
  · intro H
    refine ⟨wr_full rest Hnb, ?_⟩
    change t_emit ((rest.take rest.length).map (WriteEv ch))
      (t_emit ((rest.drop rest.length).map (WriteEv ch)) T) tr
    rw [List.take_length, List.drop_length]
    rcases H with Hp | ⟨tr', rfl, Ht⟩
    · exact Or.inl Hp
    · exact Or.inr ⟨tr', rfl, Or.inr ⟨tr', rfl, Ht⟩⟩

/-- MmapSim's two traces are the binary choice of write-then-exit shapes. -/
theorem two_traces_t_alt2 (bf : List (List byte)) (cf : word) (bs : List (List byte))
    (cs : word) (fs : Fs.Fs) (tr : List event) :
    t_alt2 (t_writes bf (t_exit cf fs)) (t_writes bs (t_exit cs fs)) tr ↔
      MmapSim.two_traces bf cf bs cs fs tr := by
  unfold t_alt2 MmapSim.two_traces
  rw [t_writes_exit_iff, t_writes_exit_iff]

/-- Exact step-family interface: every resolution is a step, and every step
is a resolution. In particular the node cannot fault or be unmodeled.
This is the per-binary proof interface: the `*_ok` lemma supplies clause 1,
and the `sstep_*_inv` lemma supplies clause 2. -/
def node_ok (segs : List Segment) (c : config) (I : Type)
    (evs : I → List event) (nx : I → config) : Prop :=
  (∀ i, sstep segs c (evs i) (SNext (nx i))) ∧
  (∀ e st, sstep segs c e st → ∃ i, e = evs i ∧ st = SNext (nx i))

/-- One realization relation for all shapes; nodes carry a witness resolution. -/
inductive realizes (segs : List Segment) : config → TSet → Prop
  | rz_node : ∀ c (I : Type) (evs : I → List event) (nx : I → config)
      (T : I → TSet) (_i0 : I), node_ok segs c I evs nx →
      (∀ i, realizes segs (nx i) (T i)) →
      realizes segs c (t_alt (fun i => t_emit (evs i) (T i)))
  | rz_halt : ∀ c, m_halted c.cfg_model ≠ none → realizes segs c t_nil
  | rz_conseq : ∀ c T T', realizes segs c T → t_eq T T' → realizes segs c T'

open realizes

theorem realizes_nonempty (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) : T [] := by
  induction H with
  | rz_node c I evs nx T i0 Hnode Hcont IH => exact ⟨i0, t_emit_has_nil _ _⟩
  | rz_halt => rfl
  | rz_conseq c T T' H Heq IH => exact (Heq []).1 IH

theorem realizes_pclosed (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) : ∀ tr tr', T tr → is_prefix tr' tr → T tr' := by
  induction H with
  | rz_node c I evs nx T i0 Hnode Hcont IH =>
    intro tr tr' HT Hp
    obtain ⟨i, Hpre | ⟨tr0, rfl, HT0⟩⟩ := HT
    · exact ⟨i, Or.inl (is_prefix_trans _ _ _ Hp Hpre)⟩
    · rcases is_prefix_app_split (evs i) tr0 tr' Hp with Hpre | ⟨tr0', Heq, Htail⟩
      · exact ⟨i, Or.inl Hpre⟩
      · exact ⟨i, Or.inr ⟨tr0', Heq, IH i tr0 tr0' HT0 Htail⟩⟩
  | rz_halt =>
    intro tr tr' HT Hp
    obtain rfl := HT
    exact is_prefix_nil_r _ Hp
  | rz_conseq c T T' H Heq IH =>
    intro tr tr' HT Hp
    exact (Heq tr').1 (IH tr tr' ((Heq tr).2 HT) Hp)

theorem realizes_star_only (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) : ∀ tr c', star segs c tr c' → T tr := by
  induction H with
  | rz_node c I evs nx T i0 Hnode Hcont IH =>
    intro tr c' Hstar
    cases Hstar with
    | star_refl => exact ⟨i0, t_emit_has_nil _ _⟩
    | star_step c e c2 tr2 c3 Hss Hstar2 =>
      obtain ⟨i, rfl, Heq⟩ := Hnode.2 _ _ Hss
      cases Heq
      exact ⟨i, Or.inr ⟨tr2, rfl, IH i _ _ Hstar2⟩⟩
  | rz_halt c Hh =>
    intro tr c' Hstar
    exact (star_from_halted segs c tr c' Hstar Hh).1
  | rz_conseq c T T' H Heq IH =>
    intro tr c' Hstar
    exact (Heq tr).1 (IH tr c' Hstar)

theorem realizes_admits (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) : ∀ tr, T tr → obs_trace segs c tr := by
  induction H with
  | rz_node c I evs nx T i0 Hnode Hcont IH =>
    intro tr HT
    obtain ⟨i, Hpre | ⟨tr0, rfl, HT0⟩⟩ := HT
    · exact ⟨evs i, nx i, star_one segs _ _ _ (Hnode.1 i), Hpre⟩
    · obtain ⟨tr'', c'', Hstar, Hp⟩ := IH i tr0 HT0
      exact ⟨evs i ++ tr'', c'', star.star_step _ _ _ _ _ (Hnode.1 i) Hstar,
        is_prefix_app_mono _ _ _ Hp⟩
  | rz_halt =>
    intro tr HT
    obtain rfl := HT
    exact obs_trace_nil _ _
  | rz_conseq c T T' H Heq IH =>
    intro tr HT
    exact IH tr ((Heq tr).2 HT)

/-- Master observation theorem: shape membership is exactly trace-prefix
membership, with no additional closure operator. -/
theorem realizes_obs_iff (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) (tr : List event) : obs_trace segs c tr ↔ T tr := by
  constructor
  · rintro ⟨tr', c', Hstar, Hp⟩
    exact realizes_pclosed segs c T H tr' tr (realizes_star_only segs c T H tr' c' Hstar) Hp
  · exact realizes_admits segs c T H tr

theorem sstep_halted_none (segs : List Segment) (c : config) (e : List event) (st : step_to)
    (H : sstep segs c e st) : m_halted c.cfg_model = none := sstep_from_running _ _ _ _ H

theorem realizes_step (segs : List Segment) (c : config) (T : TSet) (e : List event) (c' : config)
    (H : realizes segs c T) (Hss : sstep segs c e (SNext c')) : ∃ T', realizes segs c' T' := by
  induction H generalizing e c' with
  | rz_node c I evs nx T i0 Hnode Hcont IH =>
    obtain ⟨i, _, Heq⟩ := Hnode.2 _ _ Hss
    cases Heq
    exact ⟨T i, Hcont i⟩
  | rz_halt c Hh => exact False.elim (Hh (sstep_halted_none _ _ _ _ Hss))
  | rz_conseq c T T' H Heq IH => exact IH _ _ Hss

theorem realizes_no_sserror (segs : List Segment) (c : config) (T : TSet) (e : List event)
    (H : realizes segs c T) : ¬ sstep segs c e SError := by
  induction H generalizing e with
  | rz_node c I evs nx T i0 Hnode Hcont IH =>
    intro Hss
    obtain ⟨i, _, Hbad⟩ := Hnode.2 _ _ Hss
    cases Hbad
  | rz_halt c Hh => exact fun Hss => Hh (sstep_halted_none _ _ _ _ Hss)
  | rz_conseq c T T' H Heq IH => exact IH e

def rz_path (segs : List Segment) (c : config) : Prop := ∃ T, realizes segs c T

/-- Exact indexed nodes give the omni safety judgment for every finite prefix. -/
theorem realizes_cosafe (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) : cosafe segs c T :=
  star_cosafe segs c T (realizes_star_only segs c T H)

/-- Every ending execution halts with a trace in the realized shape. -/
theorem realizes_coexec (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) : coexec segs c (fun tr o => T tr ∧ ¬ is_error o) := by
  induction H with
  | rz_node c I evs nx T i0 Hnode Hcont IH =>
    apply coexec.coexec_step segs c
    · exact sstep_halted_none _ _ _ _ (Hnode.1 i0)
    · intro e Hss
      obtain ⟨i, _, Hbad⟩ := Hnode.2 _ _ Hss
      cases Hbad
    · intro e c' Hss
      obtain ⟨i, rfl, Heq⟩ := Hnode.2 _ _ Hss
      cases Heq
      exact coexec_conseq _ _ _ _ (IH i)
        (fun tr o ⟨HT, Hno⟩ => ⟨⟨i, Or.inr ⟨tr, rfl, HT⟩⟩, Hno⟩)
  | rz_halt c Hh => exact coexec.coexec_halt segs c _ Hh ⟨rfl, fun h => h⟩
  | rz_conseq c T T' H Heq IH =>
    exact coexec_conseq _ _ _ _ IH (fun tr o ⟨HT, Hno⟩ => ⟨(Heq tr).1 HT, Hno⟩)

theorem realizes_no_error (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) : ¬ reaches_error segs c := by
  apply coexec_no_error
  exact coexec_conseq _ _ _ _ (realizes_coexec segs c T H) (fun _ _ h => h.2)

/-- A realized shape cannot use the all-executions-error escape: an execution
witness for `errors` contradicts its coexecution judgment. -/
theorem realizes_not_errors (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) : ¬ exec segs c errors := by
  intro Hex
  obtain ⟨tr, o, Hm, Herr⟩ := exec_realizes _ _ _ Hex
  exact (coexec_sound _ _ _ _ Hm _ (realizes_coexec segs c T H)).2 Herr

/-- Every shape trace is produced: a prefix postcondition excluding one
of them is refuted. That postcondition is prefix-closed, so it is a
candidate for `omni_trace_equiv`. -/
theorem realizes_refutes_excluding (segs : List Segment) (c : config) (T : TSet) (tr : List event)
    (H : realizes segs c T) (HT : T tr) : ¬ cosafe segs c (fun tr' => ¬ is_prefix tr tr') := by
  intro Hc
  obtain ⟨tr', c', Hstar, Hp⟩ := realizes_admits segs c T H tr HT
  exact cosafe_star _ _ _ _ _ Hc Hstar Hp

theorem t_alt_unit (f : Unit → TSet) : t_eq (t_alt f) (f ()) := by
  intro tr
  constructor
  · rintro ⟨⟨⟩, Hf⟩
    exact Hf
  · exact fun Hf => ⟨(), Hf⟩

/-- A silent singleton node collapses to its continuation. -/
theorem rz_silent1 (segs : List Segment) (c c' : config) (T : TSet)
    (Hnode : node_ok segs c Unit (fun _ => []) (fun _ => c'))
    (Hc : realizes segs c' T) : realizes segs c T :=
  rz_conseq c _ T (rz_node c Unit (fun _ => []) (fun _ => c') (fun _ => T) () Hnode
    (fun _ => Hc)) (t_eq_trans _ _ _ (t_alt_unit _) (t_emit_nil_eq T (realizes_nonempty _ _ _ Hc)))

/-- A singleton node emitting a block. -/
theorem rz_emit1 (segs : List Segment) (c c' : config) (e : List event) (T : TSet)
    (Hnode : node_ok segs c Unit (fun _ => e) (fun _ => c'))
    (Hc : realizes segs c' T) : realizes segs c (t_emit e T) :=
  rz_conseq c _ _ (rz_node c Unit (fun _ => e) (fun _ => c') (fun _ => T) () Hnode
    (fun _ => Hc)) (t_alt_unit _)

/-- Silent two-way choice: all resolutions in each summand have the same
continuation shape, as in the mmap/brk pattern. -/
theorem rz_alt2 (segs : List Segment) (c : config) (IA IB : Type) (nx : IA ⊕ IB → config)
    (A B : TSet) (a0 : IA) (b0 : IB)
    (Hnode : node_ok segs c (IA ⊕ IB) (fun _ => []) nx)
    (HA : ∀ i, realizes segs (nx (.inl i)) A) (HB : ∀ i, realizes segs (nx (.inr i)) B) :
    realizes segs c (t_alt2 A B) := by
  have HA0 := realizes_nonempty _ _ _ (HA a0)
  have HB0 := realizes_nonempty _ _ _ (HB b0)
  refine rz_conseq c _ _ (rz_node c (IA ⊕ IB) (fun _ => []) nx
    (fun i => match i with | .inl _ => A | .inr _ => B) (.inl a0) Hnode ?_) ?_
  · intro i
    cases i with
    | inl i => exact HA i
    | inr i => exact HB i
  · intro tr
    constructor
    · rintro ⟨i, Hi⟩
      cases i with
      | inl i => exact Or.inl ((t_emit_nil_eq A HA0 tr).1 Hi)
      | inr i => exact Or.inr ((t_emit_nil_eq B HB0 tr).1 Hi)
    · rintro (H | H)
      · exact ⟨.inl a0, (t_emit_nil_eq A HA0 tr).2 H⟩
      · exact ⟨.inr b0, (t_emit_nil_eq B HB0 tr).2 H⟩

theorem node_instr (segs : List Segment) (ms : machine_state) (model : Model) (ms' : machine_state)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = none) (Hstep : step segs ms = MachineOk ms') :
    node_ok segs (config.mkCfg ms model) Unit (fun _ => []) (fun _ => config.mkCfg ms' model) := by
  constructor
  · intro _
    exact sstep.sstep_instr _ _ _ _ Hh Hsvc
      (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])
  · intro e st Hss
    obtain ⟨rfl, rfl⟩ := sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep Hss
    exact ⟨(), rfl, rfl⟩

theorem rz_step (segs : List Segment) (ms : machine_state) (model : Model) (ms' : machine_state)
    (T : TSet) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = none) (Hstep : step segs ms = MachineOk ms')
    (Hc : realizes segs (config.mkCfg ms' model) T) : realizes segs (config.mkCfg ms model) T :=
  rz_silent1 _ _ _ _ (node_instr segs ms model ms' Hh Hlazy Hsvc Hstep) Hc

theorem rz_msteps (segs : List Segment) (ms ms' : machine_state) (model : Model) (T : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hms : msteps segs ms ms')
    (Hc : realizes segs (config.mkCfg ms' model) T) : realizes segs (config.mkCfg ms model) T := by
  induction Hms with
  | mst_refl => exact Hc
  | mst_step ms ms1 ms2 Hsvc Hstep Hms IH =>
    exact rz_step segs ms model ms1 T Hh Hlazy Hsvc Hstep (IH Hc)

/-- The channel-1 write node has one resolution for every nonempty
prefix of the buffer. -/
theorem node_write1 (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (buf : List byte) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 64)
    (Hg : ms_gpr ms 0 = Z_to_bv 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hbm : buf_modeled buf) (Hnb : 1 ≤ buf.length) :
    node_ok segs (config.mkCfg ms model) (wr_index buf)
      (fun i => (buf.take i.val).map (WriteEv (Z_to_bv 64 1)))
      (fun i => config.mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take i.val)))) model) := by
  constructor
  · rintro ⟨n, Hn1, Hn2⟩
    change sstep segs (config.mkCfg ms model) _
      (SNext (config.mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model))
    rw [← apply_effect_copyins_no_write ms (len_word (buf.take n)) [(ms_gpr ms 1, n)]]
    exact sstep.sstep_syscall ms model x8 _ model model _ Hh Hsvc
      (write1_ok_n segs ms x8 model buf n Hfd Hno Hg Hr Hbm Hn1 Hn2) Hh
      (materialize_model_accesses_no_lazy _ _ Hlazy)
  · intro e st Hss
    obtain ⟨n, Hn1, Hn2, rfl, rfl⟩ :=
      sstep_write_inv segs ms model x8 buf e st Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hss
    exact ⟨⟨n, Hn1, Hn2⟩, rfl, rfl⟩

theorem rz_write1 (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (buf : List byte) (T : TSet) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 64)
    (Hg : ms_gpr ms 0 = Z_to_bv 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hbm : buf_modeled buf) (Hnb : 1 ≤ buf.length)
    (Hc : ∀ n, 1 ≤ n → n ≤ buf.length →
      realizes segs (config.mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model) T) :
    realizes segs (config.mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T) :=
  rz_node _ (wr_index buf) _ _ (fun _ => T) (wr_full buf Hnb)
    (node_write1 segs ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb)
    (fun i => Hc i.val i.property.1 i.property.2)

/-- The exit leaf. -/
theorem rz_exit (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8) (Hx8 : is_exit_no x8) :
    realizes segs (config.mkCfg ms model)
      (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)) := by
  let code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)
  apply rz_emit1 segs (config.mkCfg ms model) (config.mkCfg ms (with_halted code model))
  · constructor
    · intro _
      exact sstep.sstep_exit ms model x8 _ _ [] code Hh Hsvc
        (exit_dispatch_ok _ model Hx8) rfl rfl
    · intro e st Hss
      obtain ⟨rfl, rfl⟩ := sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss
      exact ⟨(), rfl, rfl⟩
  · apply rz_halt
    intro H
    cases H

open LinuxProcessSemantics.Common.MmapSim
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap

/-- The silent, model-changing munmap node. -/
theorem rz_munmap (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (T : TSet) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 215)
    (Hargs : munmap_args_ok ms model)
    (Hc : realizes segs
      (config.mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T) :
    realizes segs (config.mkCfg ms model) T := by
  apply rz_silent1 segs _ _ T _ Hc
  constructor
  · intro _
    exact sstep.sstep_syscall ms model x8 _ _ _ [] Hh Hsvc
      (munmap_ok segs ms x8 model Hno Hargs)
      ((munmap_model_halted _ _ _).trans Hh)
      (materialize_model_accesses_no_lazy _ _ (munmap_model_no_lazy _ _ _ Hlazy))
  · intro e st Hss
    obtain ⟨rfl, rfl⟩ := sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss
    exact ⟨(), rfl, rfl⟩

/-- Errno resolutions continue as A; grantable addresses continue as B. -/
theorem rz_mmap (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (A B : TSet) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 222)
    (Hargs : mmap_args_ok ms)
    (HA : ∀ e, e ∈ mmap_errnos →
      realizes segs (config.mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A)
    (HB : ∀ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true →
      realizes segs
        (config.mkCfg
          (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
          (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B)
    (Hex : ∃ a, grant_ok (ms_gpr ms 0) model a
      (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) :
    realizes segs (config.mkCfg ms model) (t_alt2 A B) := by
  let n := page_round_up (ms_gpr ms 1)
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1))
  obtain ⟨a0, Ha0⟩ := Hex
  let IA := {e : Int // e ∈ mmap_errnos}
  let IB := {a : word // grant_ok (ms_gpr ms 0) model a nZ = true}
  let nx : IA ⊕ IB → config := fun i => match i with
    | .inl e => config.mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e.val))) model
    | .inr a => config.mkCfg (advance_past_svc (apply_effect ms (mkEffect a.val [] [(a.val, n)])))
        (mmap_model a.val n model)
  apply rz_alt2 segs _ IA IB nx A B ⟨ENOMEM, ENOMEM_in_mmap_errnos⟩ ⟨a0, Ha0⟩
  · constructor
    · intro i
      cases i with
      | inl e =>
        change sstep segs _ [] (SNext (config.mkCfg
          (advance_past_svc (set_gpr0 ms (errno_ret e.val))) model))
        rw [← apply_effect_no_write ms (errno_ret e.val)]
        exact sstep.sstep_syscall ms model x8 _ model model [] Hh Hsvc
          (mmap_fail_ok segs ms x8 model e.val Hno Hargs e.property) Hh
          (materialize_model_accesses_no_lazy _ _ Hlazy)
      | inr a =>
        exact sstep.sstep_syscall ms model x8 _ _ _ [] Hh Hsvc
          (mmap_succ_ok segs ms x8 model a.val Hno Hargs a.property)
          ((mmap_model_halted _ _ _).trans Hh)
          (materialize_model_accesses_no_lazy _ _ ((mmap_model_lazy _ _ _).trans Hlazy))
    · intro e st Hss
      obtain ⟨rfl, Hres⟩ := sstep_mmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss
      rcases Hres with ⟨er, Her, rfl⟩ | ⟨a, Ha, rfl⟩
      · exact ⟨.inl ⟨er, Her⟩, rfl, rfl⟩
      · exact ⟨.inr ⟨a, Ha⟩, rfl, rfl⟩
  · exact fun e => HA e.val e.property
  · exact fun a => HB a.val a.property

/-- Omni ingredients of the master theorem, one per conjunct. -/
theorem shape_omni_corun (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word)
    (rnd : EntryDraw) (lim : Int) (T : TSet) (inp : ProcInput)
    (H : realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T) :
    omni_corun (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp
      (fun tr o => T tr ∧ ¬ is_error o) := realizes_coexec _ _ _ H

theorem shape_omni_cosafe (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word)
    (rnd : EntryDraw) (lim : Int) (T : TSet) (inp : ProcInput)
    (H : realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T) :
    omni_cosafe (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp T :=
  realizes_cosafe _ _ _ H

/-- Realizations of the same shape agree on every prefix-closed postcondition. -/
theorem shape_omni_trace_equiv (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (T : TSet) (inp : ProcInput)
    (Hsource : realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T)
    (Htarget : realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) T) :
    omni_trace_equiv (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd)
      (Image.mkImage target_segs apc aph) alim (ExecEntry.mkEntry asp abrk amb arnd) inp := by
  apply (trace_equiv_iff_omni _ _ _ _ _ _ _).1
  intro tr
  exact (realizes_obs_iff _ _ _ Hsource tr).trans (realizes_obs_iff _ _ _ Htarget tr).symm

theorem shape_omni_equiv (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (T : TSet) (inp : ProcInput)
    (Hsource : realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T)
    (Htarget : realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) T) :
    omni_equiv (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd)
      (Image.mkImage target_segs apc aph) alim (ExecEntry.mkEntry asp abrk amb arnd) inp := by
  refine Or.inr ⟨shape_omni_trace_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim T inp Hsource Htarget, ?_⟩
  exact coexec_conseq _ _ _ _ (realizes_coexec _ _ _ Htarget) (fun _ _ h => h.2)

/-- Master theorem at the two role budgets: a shared shape gives omni
strong equivalence, including source model coverage. -/
theorem shape_omni_strong_equiv (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw)
    (T : TSet) (inp : ProcInput)
    (Hsource : realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp) T)
    (Htarget : realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd target_alloc_limit inp) T) :
    omni_strong_equiv (Image.mkImage source_segs rpc rph) (Image.mkImage target_segs apc aph)
      (ExecEntry.mkEntry rsp rbrk rmb rrnd) (ExecEntry.mkEntry asp abrk amb arnd) inp := by
  constructor
  · exact coexec_conseq _ _ _ _ (realizes_coexec _ _ _ Hsource)
      (fun tr o h => never_errors_covered _ tr o h.2)
  · exact shape_omni_equiv source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit target_segs apc aph asp abrk amb arnd target_alloc_limit T inp Hsource Htarget

/-- A shared shape gives equivalence and source model coverage, through the
omni compatibility equivalences. The shape is the two binary proofs' interface. -/
theorem shape_strong_equiv (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (T : TSet) (inp : ProcInput)
    (Hsource : realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T)
    (Htarget : realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) T) :
    modeled (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp) ∧
    equiv (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp)
      (run (Image.mkImage target_segs apc aph) alim (ExecEntry.mkEntry asp abrk amb arnd) inp) := by
  constructor
  · apply (modeled_iff _ _ _ _).2
    exact coexec_conseq _ _ _ _ (realizes_coexec _ _ _ Hsource)
      (fun tr o h => never_errors_covered _ tr o h.2)
  · exact (equiv_iff _ _ _ _ _ _ _).2 (shape_omni_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim T inp Hsource Htarget)

/-- CatSim's write-and-exit relation realizes the per-delivery write shape. -/
theorem cat_realizes (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model) (Hte : to_wexit segs ms bufs code)
    (Hbm : bufs_modeled bufs) :
    realizes segs (config.mkCfg ms model) (t_writes_pick bufs (t_exit code (m_fs model))) := by
  induction Hte generalizing model with
  | tw_exit ms x8 Hsvc Hx8 => exact rz_exit segs ms model x8 Hh Hsvc Hx8
  | tw_write ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH =>
    have Hb : buf_modeled buf := Hbm buf (List.mem_cons_self ..)
    have Hbs : bufs_modeled bufs := fun b Hb => Hbm b (List.mem_cons_of_mem _ Hb)
    exact rz_write1 segs ms model x8 buf _ Hh Hlazy Hfd Hsvc Hno Hg Hr Hb Hnb
      (fun n Hn1 Hn2 => IH n Hn1 Hn2 model Hh Hlazy Hfd Hbs)
  | tw_step ms ms' bufs code Hsvc Hstep Hte IH =>
    exact rz_step segs ms model ms' _ Hh Hlazy Hsvc Hstep (IH model Hh Hlazy Hfd Hbm)

/-- The exit straight line realizes the exit leaf without an fd hypothesis. -/
theorem exitline_realizes_aux (segs : List Segment) (ms : machine_state) (bufs : List (List byte))
    (code : word) (model : Model) (Hte : to_wexit segs ms bufs code) (Hbufs : bufs = [])
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    realizes segs (config.mkCfg ms model) (t_exit code (m_fs model)) := by
  induction Hte with
  | tw_exit ms x8 Hsvc Hx8 => exact rz_exit segs ms model x8 Hh Hsvc Hx8
  | tw_write => cases Hbufs
  | tw_step ms ms' bufs code Hsvc Hstep Hte IH =>
    exact rz_step segs ms model ms' _ Hh Hlazy Hsvc Hstep (IH Hbufs)

theorem exitline_realizes (segs : List Segment) (ms : machine_state) (code : word) (model : Model)
    (Hte : to_wexit segs ms [] code) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    realizes segs (config.mkCfg ms model) (t_exit code (m_fs model)) :=
  exitline_realizes_aux segs ms [] code model Hte rfl Hh Hlazy

/-- Collapse the write-all retry loop while retaining its arbitrary continuation. -/
theorem rz_wall1_mut (segs : List Segment) (model : Model)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model) :
    (∀ ms rest k, to_wall segs (Z_to_bv 64 1) ms rest k →
      buf_modeled rest → ∀ T : TSet, T [] →
      (∀ ms', k ms' → realizes segs (config.mkCfg ms' model) T) →
      realizes segs (config.mkCfg ms model) (t_emit (rest.map (WriteEv (Z_to_bv 64 1))) T)) ∧
    (∀ ms rest k, to_wall_tail segs (Z_to_bv 64 1) ms rest k →
      buf_modeled rest → ∀ T : TSet, T [] →
      (∀ ms', k ms' → realizes segs (config.mkCfg ms' model) T) →
      realizes segs (config.mkCfg ms model) (t_emit (rest.map (WriteEv (Z_to_bv 64 1))) T)) := by
  apply to_wall_mutind segs (Z_to_bv 64 1)
    (fun ms rest k => buf_modeled rest → ∀ T : TSet, T [] →
      (∀ ms', k ms' → realizes segs (config.mkCfg ms' model) T) →
      realizes segs (config.mkCfg ms model) (t_emit (rest.map (WriteEv (Z_to_bv 64 1))) T))
    (fun ms rest k => buf_modeled rest → ∀ T : TSet, T [] →
      (∀ ms', k ms' → realizes segs (config.mkCfg ms' model) T) →
      realizes segs (config.mkCfg ms model) (t_emit (rest.map (WriteEv (Z_to_bv 64 1))) T))
  · intro ms x8 rest k Hsvc Hno Hg Hr Hnb _ IH Hbm T HT Hk
    refine rz_conseq _ _ _ (rz_node _ (wr_index rest)
      (fun i => (rest.take i.val).map (WriteEv (Z_to_bv 64 1)))
      (fun i => config.mkCfg (advance_past_svc (set_gpr0 ms (len_word (rest.take i.val)))) model)
      (fun i => t_emit ((rest.drop i.val).map (WriteEv (Z_to_bv 64 1))) T)
      (wr_full rest Hnb) (node_write1 segs ms model x8 rest Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb)
      ?_) (t_alt_wall _ rest T HT Hnb)
    exact fun i => IH i.val i.property.1 i.property.2 (buf_modeled_skipn i.val rest Hbm) T HT Hk
  · intro ms k Hk _ T HT Hcont
    exact rz_conseq _ _ _ (Hcont ms Hk) (t_eq_sym _ _ (t_emit_nil_eq T HT))
  · intro ms rest k _ _ IH Hbm T HT Hk
    exact IH Hbm T HT Hk
  · intro ms ms' rest k Hsvc Hstep _ IH Hbm T HT Hk
    exact rz_step segs ms model ms' _ Hh Hlazy Hsvc Hstep (IH Hbm T HT Hk)

/-- The retry-loop list realizes full delivery, independently of chunking. -/
theorem wall_realizes (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model)
    (Hw : to_wallexit segs (Z_to_bv 64 1) bufs code ms) (Hbm : bufs_modeled bufs) :
    realizes segs (config.mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))) := by
  induction bufs generalizing ms with
  | nil => exact exitline_realizes segs ms code model Hw Hh Hlazy
  | cons buf rest IH =>
    obtain ⟨_, Ht⟩ := Hw
    have Hb : buf_modeled buf := Hbm buf (List.mem_cons_self ..)
    have Hbs : bufs_modeled rest := fun b Hb => Hbm b (List.mem_cons_of_mem _ Hb)
    rw [t_writes_cons]
    exact (rz_wall1_mut segs model Hh Hlazy Hfd).2 ms buf _ Ht Hb _
      (t_writes_ch_exit_has_nil _ rest code _) (fun ms' Hk => IH ms' Hk Hbs)

/-- MmapSim's mutual retry-loop derivations collapse to full delivery too. -/
theorem twm_realizes_mut (segs : List Segment) :
    (∀ ms model bufs code, MmapSim.twm segs ms model bufs code →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled bufs →
      realizes segs (config.mkCfg ms model) (t_writes bufs (t_exit code (m_fs model)))) ∧
    (∀ ms model rest bufs code, MmapSim.twm_pend segs ms model rest bufs code →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      buf_modeled rest → bufs_modeled bufs →
      realizes segs (config.mkCfg ms model)
        (t_emit (rest.map (WriteEv (Z_to_bv 64 1))) (t_writes bufs (t_exit code (m_fs model))))) ∧
    (∀ ms model rest bufs code, MmapSim.twm_tail segs ms model rest bufs code →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      buf_modeled rest → bufs_modeled bufs →
      realizes segs (config.mkCfg ms model)
        (t_emit (rest.map (WriteEv (Z_to_bv 64 1))) (t_writes bufs (t_exit code (m_fs model))))) := by
  apply MmapSim.twm_mutind segs
    (fun ms model bufs code =>
      m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled bufs →
      realizes segs (config.mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
    (fun ms model rest bufs code =>
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      buf_modeled rest → bufs_modeled bufs →
      realizes segs (config.mkCfg ms model)
        (t_emit (rest.map (WriteEv (Z_to_bv 64 1))) (t_writes bufs (t_exit code (m_fs model)))))
    (fun ms model rest bufs code =>
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      buf_modeled rest → bufs_modeled bufs →
      realizes segs (config.mkCfg ms model)
        (t_emit (rest.map (WriteEv (Z_to_bv 64 1))) (t_writes bufs (t_exit code (m_fs model)))))
  · intro ms model x8 Hsvc Hx8 Hh _ _ _
    exact rz_exit segs ms model x8 Hh Hsvc Hx8
  · intro ms model buf bufs code _ _ IH Hh Hlazy Hfd Hbm
    exact IH Hh Hlazy Hfd (Hbm buf (List.mem_cons_self ..))
      (fun b Hb => Hbm b (List.mem_cons_of_mem _ Hb))
  · intro ms model x8 bufs code Hsvc Hno Hargs _ IH Hh Hlazy Hfd Hbm
    apply rz_munmap segs ms model x8 _ Hh Hlazy Hsvc Hno Hargs
    rw [← munmap_model_fs (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model]
    exact IH ((munmap_model_halted _ _ _).trans Hh)
      (munmap_model_no_lazy _ _ _ Hlazy) (munmap_model_fd1chan _ _ _ Hfd) Hbm
  · intro ms ms' model bufs code Hsvc Hstep _ IH Hh Hlazy Hfd Hbm
    exact rz_step segs ms model ms' _ Hh Hlazy Hsvc Hstep (IH Hh Hlazy Hfd Hbm)
  · intro ms model x8 rest bufs code Hsvc Hno Hg Hr Hnb _ IH Hh Hlazy Hfd Hbr Hbm
    refine rz_conseq _ _ _ (rz_node _ (wr_index rest)
      (fun i => (rest.take i.val).map (WriteEv (Z_to_bv 64 1)))
      (fun i => config.mkCfg (advance_past_svc (set_gpr0 ms (len_word (rest.take i.val)))) model)
      (fun i => t_emit ((rest.drop i.val).map (WriteEv (Z_to_bv 64 1)))
        (t_writes bufs (t_exit code (m_fs model))))
      (wr_full rest Hnb) (node_write1 segs ms model x8 rest Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr Hnb)
      ?_) (t_alt_wall _ rest _ (t_writes_ch_exit_has_nil _ bufs code _) Hnb)
    exact fun i => IH i.val i.property.1 i.property.2 Hh Hlazy Hfd
      (buf_modeled_skipn i.val rest Hbr) Hbm
  · intro ms model bufs code _ IH Hh Hlazy Hfd _ Hbm
    exact rz_conseq _ _ _ (IH Hh Hlazy Hfd Hbm)
      (t_eq_sym _ _ (t_emit_nil_eq _ (t_writes_ch_exit_has_nil _ bufs code _)))
  · intro ms model rest bufs code _ _ IH Hh Hlazy Hfd Hbr Hbm
    exact IH Hh Hlazy Hfd Hbr Hbm
  · intro ms ms' model rest bufs code Hsvc Hstep _ IH Hh Hlazy Hfd Hbr Hbm
    exact rz_step segs ms model ms' _ Hh Hlazy Hsvc Hstep (IH Hh Hlazy Hfd Hbr Hbm)

theorem twm_realizes (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model) (Hte : MmapSim.twm segs ms model bufs code)
    (Hbm : bufs_modeled bufs) :
    realizes segs (config.mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))) :=
  (twm_realizes_mut segs).1 ms model bufs code Hte Hh Hlazy Hfd Hbm

/-- A deterministic prefix followed by mmap realizes a binary alternative. -/
theorem tmw_realizes (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model)
    (Hte : MmapSim.tmw segs ms model bf cf bs cs) (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    realizes segs (config.mkCfg ms model)
      (t_alt2 (t_writes bf (t_exit cf (m_fs model))) (t_writes bs (t_exit cs (m_fs model)))) := by
  induction Hte with
  | tmw_mmap ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail Hsucc Hex =>
    apply rz_mmap segs ms model x8 _ _ Hh Hlazy Hsvc Hno Hargs _ _ Hex
    · exact fun e He => twm_realizes segs _ model bf cf Hh Hlazy Hfd (Hfail e He) Hbf
    · intro a Ha
      rw [← mmap_model_fs a (page_round_up (ms_gpr ms 1)) model]
      exact twm_realizes segs _ _ bs cs ((mmap_model_halted _ _ _).trans Hh)
        ((mmap_model_lazy _ _ _).trans Hlazy) (mmap_model_fd1chan _ _ _ Hfd) (Hsucc a Ha) Hbs
  | tmw_step ms ms' model bf cf bs cs Hsvc Hstep _ IH =>
    exact rz_step segs ms model ms' _ Hh Hlazy Hsvc Hstep (IH Hh Hlazy Hfd Hbf Hbs)

/-- Cat write-and-exit equivalence derived from the generic shape theorem. -/
theorem cat_strong_equiv_alg (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (bufs : List (List byte)) (code : word) (inp : ProcInput)
    (Hs : to_wexit source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      bufs code)
    (Ht : to_wexit target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      bufs code)
    (Hbm : bufs_modeled bufs) :
    modeled (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp) ∧
    equiv (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp)
      (run (Image.mkImage target_segs apc aph) alim (ExecEntry.mkEntry asp abrk amb arnd) inp) := by
  apply shape_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim (t_writes_pick bufs (t_exit code inp.in_fs)) inp
  · exact cat_realizes source_segs _ _ bufs code rfl rfl rfl Hs Hbm
  · exact cat_realizes target_segs _ _ bufs code rfl rfl rfl Ht Hbm

/-- Cat write-and-exit equivalence derived from the generic shape theorem at the two role budgets. -/
theorem cat_omni_strong_equiv_alg (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw)
    (bufs : List (List byte)) (code : word) (inp : ProcInput)
    (Hs : to_wexit source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      bufs code)
    (Ht : to_wexit target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      bufs code)
    (Hbm : bufs_modeled bufs) :
    omni_strong_equiv (Image.mkImage source_segs rpc rph) (Image.mkImage target_segs apc aph)
      (ExecEntry.mkEntry rsp rbrk rmb rrnd) (ExecEntry.mkEntry asp abrk amb arnd) inp := by
  apply shape_omni_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd (t_writes_pick bufs (t_exit code inp.in_fs)) inp
  · exact cat_realizes source_segs _ _ bufs code rfl rfl rfl Hs Hbm
  · exact cat_realizes target_segs _ _ bufs code rfl rfl rfl Ht Hbm

def t_writes_ch_pick (ch : word) (bufs : List (List byte)) (T : TSet) : TSet :=
  bufs.foldr (t_write_ch ch) T

theorem t_writes_ch_pick_1 (bufs : List (List byte)) (T : TSet) :
    t_writes_ch_pick (Z_to_bv 64 1) bufs T = t_writes_pick bufs T := rfl

theorem t_writes_ch_pick_cons (ch : word) (buf : List byte) (bufs : List (List byte)) (T : TSet) :
    t_writes_ch_pick ch (buf :: bufs) T = t_write_ch ch buf (t_writes_ch_pick ch bufs T) := rfl

theorem node_write_ch (segs : List Segment) (ms : machine_state) (model : Model) (fd ch x8 : word)
    (buf : List byte) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model) (H32 : Sys.Syscall.fd32 fd = fd)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 64)
    (Hg : ms_gpr ms 0 = fd)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hbm : buf_modeled buf) (Hnb : 1 ≤ buf.length) :
    node_ok segs (config.mkCfg ms model) (wr_index buf)
      (fun i => (buf.take i.val).map (WriteEv ch))
      (fun i => config.mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take i.val)))) model) := by
  constructor
  · rintro ⟨n, Hn1, Hn2⟩
    change sstep segs (config.mkCfg ms model) _
      (SNext (config.mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model))
    rw [← apply_effect_copyins_no_write ms (len_word (buf.take n)) [(ms_gpr ms 1, n)]]
    exact sstep.sstep_syscall ms model x8 _ model model _ Hh Hsvc
      (write_ch_ok_n segs ms x8 model fd ch buf n Hfdc H32 Hno Hg Hr Hbm Hn1 Hn2) Hh
      (materialize_model_accesses_no_lazy _ _ Hlazy)
  · intro e st Hss
    obtain ⟨n, Hn1, Hn2, rfl, rfl⟩ :=
      sstep_write_ch_inv segs fd ch H32 ms model x8 buf e st Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss
    exact ⟨⟨n, Hn1, Hn2⟩, rfl, rfl⟩

theorem rz_write_ch (segs : List Segment) (ms : machine_state) (model : Model) (fd ch x8 : word)
    (buf : List byte) (T : TSet) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model) (H32 : Sys.Syscall.fd32 fd = fd)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 64)
    (Hg : ms_gpr ms 0 = fd)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hbm : buf_modeled buf) (Hnb : 1 ≤ buf.length)
    (Hc : ∀ n, 1 ≤ n → n ≤ buf.length →
      realizes segs (config.mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model) T) :
    realizes segs (config.mkCfg ms model) (t_write_ch ch buf T) :=
  rz_node _ (wr_index buf) _ _ (fun _ => T) (wr_full buf Hnb)
    (node_write_ch segs ms model fd ch x8 buf Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb)
    (fun i => Hc i.val i.property.1 i.property.2)

/-- Prefixes of the candidate trace of each brk outcome. -/
def t_outcomes (fs : Fs.Fs) (U : (List (List byte) × word) → Prop) : TSet :=
  fun tr => ∃ o, U o ∧ is_prefix tr (AllocSim.outcome_trace fs o)

theorem t_alt_emit_nil (I : Type) (f : I → TSet) (H : ∀ i, f i []) :
    t_eq (t_alt (fun i => t_emit [] (f i))) (t_alt f) := by
  intro tr
  constructor
  · rintro ⟨i, Hi⟩
    exact ⟨i, (t_emit_nil_eq (f i) (H i) tr).1 Hi⟩
  · rintro ⟨i, Hi⟩
    exact ⟨i, (t_emit_nil_eq (f i) (H i) tr).2 Hi⟩

/-- Receptivity supplies an inhabitant of the brk node's resolution index. -/
theorem outcomes_realizes (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop) (Hto : AllocSim.to_outcomes segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    realizes segs (config.mkCfg ms model) (t_outcomes (m_fs model) U) := by
  induction Hto with
  | tou_wexit ms model bufs code U Hfd Hte Hbm HU =>
    refine rz_conseq _ _ _ (wall_realizes segs ms model bufs code Hh Hlazy Hfd Hte Hbm) ?_
    intro tr
    rw [t_writes_exit_iff]
    constructor
    · intro Hp
      exact ⟨(bufs, code), (HU _).2 rfl, Hp⟩
    · rintro ⟨o, Ho, Hp⟩
      obtain rfl := (HU o).1 Ho
      exact Hp
  | tou_step ms ms' model U Hsvc Hstep _ IH =>
    exact rz_step segs ms model ms' _ Hh Hlazy Hsvc Hstep (IH Hh Hlazy)
  | tou_brk ms model x8 T U Hsvc Hno _ HU IH =>
    let P : SyscallEffect × Model → Prop := fun p =>
      syscall_spec (sys_input segs ms x8) model (Ok p.1 p.2 [])
    let nx : Subtype P → config := fun i =>
      config.mkCfg (advance_past_svc (apply_effect ms i.val.1)) i.val.2
    let Ti : Subtype P → TSet := fun i => t_outcomes (m_fs model) (T i.val.1 i.val.2)
    obtain ⟨eff0, model0, Hspec0⟩ := AllocSim.brk_receptive segs ms x8 model Hno
    have Hcont' : ∀ i : Subtype P, realizes segs (nx i) (Ti i) := by
      rintro ⟨⟨eff, model'⟩, Hspec⟩
      obtain ⟨_, Hh', Hfs, _, Hlazy'⟩ :=
        AllocSim.brk_step_shape segs ms x8 model eff model' [] Hh Hlazy Hno Hspec
      change realizes segs (config.mkCfg (advance_past_svc (apply_effect ms eff)) model')
        (t_outcomes (m_fs model) (T eff model'))
      rw [← Hfs]
      exact IH eff model' [] Hspec Hh' (Hlazy'.trans Hlazy)
    refine rz_conseq _ _ _ (rz_node _ (Subtype P) (fun _ => []) nx Ti
      ⟨(eff0, model0), Hspec0⟩ ?_ Hcont') ?_
    · constructor
      · rintro ⟨⟨eff, model'⟩, Hspec⟩
        obtain ⟨_, Hh', _, _, Hlazy'⟩ :=
          AllocSim.brk_step_shape segs ms x8 model eff model' [] Hh Hlazy Hno Hspec
        exact sstep.sstep_syscall ms model x8 eff model' model' [] Hh Hsvc Hspec Hh'
          (materialize_model_accesses_no_lazy _ _ (Hlazy'.trans Hlazy))
      · intro e st Hss
        obtain ⟨eff, model', Hspec, rfl, rfl⟩ :=
          AllocSim.sstep_brk_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hss
        exact ⟨⟨(eff, model'), Hspec⟩, rfl, rfl⟩
    · apply t_eq_trans _ _ _ (t_alt_emit_nil _ Ti (fun i => realizes_nonempty _ _ _ (Hcont' i)))
      intro tr
      constructor
      · rintro ⟨⟨⟨eff, model'⟩, Hspec⟩, o, Ho, Hp⟩
        exact ⟨o, (HU o).2 ⟨eff, model', [], Hspec, Ho⟩, Hp⟩
      · rintro ⟨o, Ho, Hp⟩
        obtain ⟨eff, model', evs, Hspec, Ht⟩ := (HU o).1 Ho
        obtain ⟨rfl, _, _, _, _⟩ :=
          AllocSim.brk_step_shape segs ms x8 model eff model' evs Hh Hlazy Hno Hspec
        exact ⟨⟨(eff, model'), Hspec⟩, o, Ht, Hp⟩

/-- `AllocSim2.two_outcomes` as a binary choice of write-then-exit shapes. -/
theorem t_outcomes_two_alt2 (fs : Fs.Fs) (bf : List (List byte)) (cf : word)
    (bs : List (List byte)) (cs : word) :
    t_eq (t_outcomes fs (AllocSim2.two_outcomes bf cf bs cs))
      (t_alt2 (t_writes bf (t_exit cf fs)) (t_writes bs (t_exit cs fs))) := by
  intro tr
  unfold t_outcomes AllocSim2.two_outcomes t_alt2
  rw [t_writes_exit_iff, t_writes_exit_iff]
  constructor
  · rintro ⟨o, rfl | rfl, Hp⟩
    · exact Or.inl Hp
    · exact Or.inr Hp
  · rintro (Hp | Hp)
    · exact ⟨(bf, cf), Or.inl rfl, Hp⟩
    · exact ⟨(bs, cs), Or.inr rfl, Hp⟩

end LinuxProcessSemantics.Common.ShapeAlg
