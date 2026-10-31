import LinuxProcessSemantics.LinuxProcessSem.Run
import LinuxProcessSemantics.LinuxProcessSem.StreamLaws

/-! rocq-baseline: 9f9a96b29a12dd26b54bff74b47ba1c4a6e01ad3
divergence: bugs/fin-record-not-injective-on-the-random-field.md -- inherited -/

/-! # EquivalenceDefinition.FinInput — finite process inputs

This file mirrors `theories/EquivalenceDefinition/FinInput.v`.
The long arguments stay on the Rocq file.

TRUST BOUNDARY: this file is part of the trusted specification.

These Rocq lemmas have no twin in this file.
`stream_decompose` has its twin in `StreamLaws.lean`: `State.stream_decompose`,
with the same statement over `uncons`.
`valid_input_tmp_arbitrary` needs `State.fs_seed_tmp_valid`, which waits on
the `fs_set_sorted` port that `Fs.lean`'s header names.
Delete this sentence when this file proves it;
`check_lean_spec_parity.py` compares definitions, not lemmas.

`all_zeros` is the Rocq CoFixpoint written as a `stream_const`, which is also
the body of `State.default_urandom`; Rocq's two streams are separate CoFixpoints.
So `to_proc_input_not_inj` unfolds the padding with `all_zeros_unfold` until
`State.stream_const_unfold`, which Rocq uses there, has a Lean twin. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.FinInput

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run

def stream_of_list : List byte → InputStream
  | [] => IEof
  | b :: l => ICons b (stream_of_list l)

def stream_of_list_then : List byte → InputStream → InputStream
  | [], s => s
  | b :: l, s => ICons b (stream_of_list_then l s)

theorem stream_of_list_then_infinite (l : List byte) (s : InputStream) :
    stream_infinite s → stream_infinite (stream_of_list_then l s) := by
  intro hs
  induction l with
  | nil => exact hs
  | cons b l ih =>
    intro i
    cases i with
    | zero => rfl
    | succ i => exact ih i

inductive finite_stream : InputStream → Prop
  | finite_stream_eof : finite_stream IEof
  | finite_stream_cons : ∀ b s, finite_stream s → finite_stream (ICons b s)

theorem finite_stream_stream_of_list (l : List byte) : finite_stream (stream_of_list l) := by
  induction l with
  | nil => exact finite_stream.finite_stream_eof
  | cons b l ih => exact finite_stream.finite_stream_cons b _ ih

theorem finite_stream_of_list (s : InputStream) :
    finite_stream s → ∃ l, s = stream_of_list l := by
  intro h
  induction h with
  | finite_stream_eof => exact ⟨[], rfl⟩
  | finite_stream_cons b s _ ih =>
    obtain ⟨l, rfl⟩ := ih
    exact ⟨b :: l, rfl⟩

theorem stream_of_list_inj (l1 l2 : List byte) :
    stream_of_list l1 = stream_of_list l2 → l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => intro _; rfl
    | cons b l => intro h; exact absurd h (IEof_ne_ICons b _)
  | cons b l ih =>
    cases l2 with
    | nil => intro h; exact absurd h (ICons_ne_IEof b _)
    | cons b' l' =>
      intro h
      obtain ⟨hb, ht⟩ := (ICons_eq_ICons b b' _ _).mp h
      rw [hb, ih l' ht]

theorem stream_take_of_list (l : List byte) (k : Nat) :
    l.length ≤ k → stream_take (stream_of_list l) k = (l, IEof) := by
  induction k generalizing l with
  | zero =>
    cases l with
    | nil => intro _; rfl
    | cons b l => intro h; simp only [List.length_cons] at h; omega
  | succ k ih =>
    cases l with
    | nil => intro _; exact stream_take_eof _
    | cons b l =>
      intro h
      have hl : l.length ≤ k := by simp only [List.length_cons] at h; omega
      simp only [stream_of_list, stream_take_cons, ih l hl]

theorem stream_take_of_list_exact (l : List byte) :
    stream_take (stream_of_list l) l.length = (l, IEof) :=
  stream_take_of_list l l.length (Nat.le_refl _)

def all_zeros : InputStream := stream_const (Z_to_bv 8 0)

theorem all_zeros_unfold : all_zeros = ICons (Z_to_bv 8 0) all_zeros := by
  apply InputStream.ext
  intro i
  cases i <;> rfl

theorem finite_stream_neq_all_zeros (s : InputStream) : finite_stream s → s ≠ all_zeros := by
  intro h
  induction h with
  | finite_stream_eof =>
    intro heq
    rw [all_zeros_unfold] at heq
    exact IEof_ne_ICons _ _ heq
  | finite_stream_cons b s _ ih =>
    intro heq
    rw [all_zeros_unfold] at heq
    exact ih ((ICons_eq_ICons _ _ _ _).mp heq).2

theorem all_zeros_not_finite : ¬ finite_stream all_zeros :=
  fun h => finite_stream_neq_all_zeros _ h rfl

theorem finite_stream_bites :
    finite_stream (stream_of_list [Z_to_bv 8 0]) ∧ ¬ finite_stream all_zeros :=
  ⟨finite_stream_stream_of_list _, all_zeros_not_finite⟩

def padded_urandom (s : InputStream) : Prop :=
  ∃ l, s = stream_of_list_then l default_urandom

def finite_input (inp : ProcInput) : Prop :=
  finite_stream inp.in_stdin ∧ padded_urandom inp.in_urandom

structure FinProcInput where
  mkFinProcInput ::
  fin_argv : List (List byte)
  fin_envp : List (List byte)
  fin_image_fs : Fs.Fs
  fin_stdin : List byte
  fin_uid : word
  fin_gid : word
  fin_groups : List word
  fin_net : NetQueue
  fin_nofile : word
  fin_sigmask : word
  fin_hwcap : word
  fin_abort_terminal : Bool
  fin_va_size : VaSize
  fin_urandom : List byte
  fin_tmp : Fs.Fs

def to_proc_input (f : FinProcInput) : ProcInput :=
  ProcInput.mkProcInput_full f.fin_argv f.fin_envp f.fin_image_fs
    (stream_of_list f.fin_stdin) f.fin_uid f.fin_gid f.fin_groups f.fin_net
    f.fin_nofile f.fin_sigmask f.fin_hwcap f.fin_abort_terminal f.fin_va_size
    (stream_of_list_then f.fin_urandom default_urandom) f.fin_tmp

def valid_fin_input (f : FinProcInput) : Prop := valid_input (to_proc_input f)

def valid_fin_input_abort (f : FinProcInput) : Prop := valid_input_abort (to_proc_input f)

structure FinCore where
  mkFinCore ::
  core_argv : List (List byte)
  core_envp : List (List byte)
  core_fs : Fs.Fs
  core_stdin : List byte

def fin_core (f : FinProcInput) : FinCore :=
  FinCore.mkFinCore f.fin_argv f.fin_envp f.fin_image_fs f.fin_stdin

theorem fin_core_env_eq (f g : FinProcInput) :
    fin_core f = fin_core g →
    f.fin_tmp = g.fin_tmp → f.fin_urandom = g.fin_urandom →
    f.fin_uid = g.fin_uid → f.fin_gid = g.fin_gid →
    f.fin_groups = g.fin_groups → f.fin_net = g.fin_net →
    f.fin_nofile = g.fin_nofile → f.fin_sigmask = g.fin_sigmask →
    f.fin_hwcap = g.fin_hwcap → f.fin_abort_terminal = g.fin_abort_terminal →
    f.fin_va_size = g.fin_va_size → f = g := by
  cases f
  cases g
  intro hc ht hr hu hg hgs hn hnf hsm hhc hab hva
  injection hc
  subst_vars
  rfl

theorem fin_core_fibre_infinite (f : FinProcInput) :
    ∃ h : Nat → FinProcInput,
      (∀ n, fin_core (h n) = fin_core f) ∧
      (∀ m n, h m = h n → m = n) ∧
      (valid_fin_input f → ∀ n, valid_fin_input (h n)) := by
  refine ⟨fun n => { f with fin_groups := List.replicate n (Z_to_bv 64 0) }, ?_, ?_, ?_⟩
  · intro _; rfl
  · intro m n heq
    have hlen := congrArg (fun g => g.fin_groups.length) heq
    simpa only [List.length_replicate] using hlen
  · intro h _; exact h

theorem finite_input_to_proc_input (f : FinProcInput) : finite_input (to_proc_input f) :=
  ⟨finite_stream_stream_of_list _, f.fin_urandom, rfl⟩

theorem to_proc_input_inj (f g : FinProcInput) :
    to_proc_input f = to_proc_input g → f.fin_urandom = g.fin_urandom → f = g := by
  intro h hr
  apply fin_core_env_eq f g
  · unfold fin_core
    have ha := congrArg ProcInput.in_argv h
    have he := congrArg ProcInput.in_envp h
    have hf := congrArg ProcInput.in_image_fs h
    have hs := stream_of_list_inj _ _ (congrArg ProcInput.in_stdin h)
    dsimp only [to_proc_input] at ha he hf
    rw [ha, he, hf, hs]
  · exact congrArg ProcInput.in_tmp h
  · exact hr
  · exact congrArg ProcInput.in_uid h
  · exact congrArg ProcInput.in_gid h
  · exact congrArg ProcInput.in_groups h
  · exact congrArg ProcInput.in_net h
  · exact congrArg ProcInput.in_nofile h
  · exact congrArg ProcInput.in_sigmask h
  · exact congrArg ProcInput.in_hwcap h
  · exact congrArg ProcInput.in_abort_terminal h
  · exact congrArg ProcInput.in_va_size h

theorem to_proc_input_not_inj :
    ∃ f g, f ≠ g ∧ to_proc_input f = to_proc_input g := by
  let base := FinProcInput.mkFinProcInput [] [] [] [] (Z_to_bv 64 0) (Z_to_bv 64 0)
    [] net_silent (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) false .Sv48 [] []
  refine ⟨base, { base with fin_urandom := [Z_to_bv 8 0] }, ?_, ?_⟩
  · intro h
    have hr := congrArg FinProcInput.fin_urandom h
    exact absurd hr (by decide)
  · dsimp only [to_proc_input, base, stream_of_list_then]
    unfold default_urandom
    have hz := all_zeros_unfold
    dsimp only [all_zeros] at hz
    rw [← hz]

theorem finite_input_surjection (inp : ProcInput) :
    finite_input inp → ∃ f, inp = to_proc_input f := by
  cases inp with
  | mkProcInput_full a e fs s u g gs n nf sm hc ab va r tm =>
    intro h
    obtain ⟨hs, lr, hr⟩ := h
    obtain ⟨l, hl⟩ := finite_stream_of_list _ hs
    refine ⟨FinProcInput.mkFinProcInput a e fs l u g gs n nf sm hc ab va lr tm, ?_⟩
    dsimp only [] at hl hr
    dsimp only [to_proc_input]
    rw [hl, hr]

theorem finite_input_iff_image (inp : ProcInput) :
    finite_input inp ↔ ∃ f, inp = to_proc_input f := by
  constructor
  · exact finite_input_surjection inp
  · intro h
    obtain ⟨f, rfl⟩ := h
    exact finite_input_to_proc_input f

theorem valid_finite_input_surjection (inp : ProcInput) :
    valid_input inp → finite_input inp → ∃ f, valid_fin_input f ∧ inp = to_proc_input f := by
  intro hv hf
  obtain ⟨f, heq⟩ := finite_input_surjection inp hf
  refine ⟨f, ?_, heq⟩
  unfold valid_fin_input
  rw [← heq]
  exact hv

theorem valid_input_stdin_irrelevant (inp : ProcInput) (s : InputStream) :
    valid_input inp → valid_input { inp with in_stdin := s } := by
  intro h; exact h

theorem valid_input_urandom_endless_irrelevant (inp : ProcInput) (r : InputStream) :
    valid_input inp → stream_infinite r → valid_input { inp with in_urandom := r } := by
  intro h hr
  unfold valid_input at h ⊢
  (repeat obtain ⟨_, h⟩ := (h : _ ∧ _))
  dsimp only [valid_creds, valid_sigmask, valid_urandom, ProcInput.in_fs] at *
  repeat' (first | with_reducible assumption | refine ⟨?_, ?_⟩)

theorem valid_fin_input_stdin_irrelevant (f : FinProcInput) (l : List byte) :
    valid_fin_input f → valid_fin_input { f with fin_stdin := l } := by
  intro h; exact h

theorem valid_fin_input_urandom_irrelevant (f : FinProcInput) (l : List byte) :
    valid_fin_input f → valid_fin_input { f with fin_urandom := l } := by
  intro h
  exact valid_input_urandom_endless_irrelevant (to_proc_input f)
    (stream_of_list_then l default_urandom) h
    (stream_of_list_then_infinite l default_urandom default_urandom_infinite)

def inhabited_fin_input : FinProcInput :=
  FinProcInput.mkFinProcInput [[]] [] [] [] (Z_to_bv 64 0) (Z_to_bv 64 0) [] net_silent
    default_nofile (Z_to_bv 64 0) StackLayout.hwcap_rv64gc false .Sv48 [] []

theorem valid_fin_input_inhabited : ∃ f, valid_fin_input f := by
  refine ⟨inhabited_fin_input, ?_⟩
  unfold valid_fin_input valid_input
  repeat' with_reducible apply And.intro
  all_goals first
    | (simp only [valid_argv, valid_envp, Fs.valid_fs, valid_creds, valid_id,
        valid_nofile, valid_sigmask, valid_hwcap]
       set_option maxRecDepth 32768 in decide)
    | rfl
    | -- `Fs.fs_keys_relative` on the empty image, the clause f1006fe8 puts
      -- where `Fs.fs_image_real … = true` used to be.  It is a bounded ∀
      -- over a `match`-defined Prop, so `decide` finds no instance for it.
      (unfold Fs.fs_keys_relative; intro pf hpf; cases hpf)
    | exact default_urandom_infinite
    | fail "valid_fin_input: a clause matched none of the shapes"

theorem valid_and_finite_inhabited : ∃ inp, valid_input inp ∧ finite_input inp := by
  obtain ⟨f, h⟩ := valid_fin_input_inhabited
  exact ⟨to_proc_input f, h, finite_input_to_proc_input f⟩

theorem valid_input_not_finite (inp : ProcInput) :
    valid_input inp → valid_input { inp with in_stdin := all_zeros } ∧
      ¬ finite_input { inp with in_stdin := all_zeros } := by
  intro h
  refine ⟨valid_input_stdin_irrelevant inp all_zeros h, ?_⟩
  intro hf
  exact all_zeros_not_finite hf.1

end LinuxProcessSemantics.EquivalenceDefinition.FinInput
