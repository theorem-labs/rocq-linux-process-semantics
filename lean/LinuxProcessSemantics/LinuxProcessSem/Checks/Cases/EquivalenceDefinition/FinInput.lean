import LinuxProcessSemantics.EquivalenceDefinition.FinInput

/-! # Checks.Cases.EquivalenceDefinition.FinInput — the finite-input record at concrete records

Not part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.FinInput

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.FinInput

/-! ## A-FinInput: the finite-input record at concrete records -/

def launch : FinProcInput :=
  { inhabited_fin_input with
    fin_stdin := [Z_to_bv 8 0x61]
    fin_uid := Z_to_bv 64 1000
    fin_gid := Z_to_bv 64 1000
    fin_urandom := [Z_to_bv 8 0x2a] }

/-- `valid_fin_input` accepts a concrete launch record.
model: `Run.valid_input` at `to_proc_input`'s image of a concrete record; `to_proc_input` pads the random list with `State.default_urandom`. -/
theorem launch_is_valid : valid_fin_input launch := by
  unfold valid_fin_input valid_input
  repeat' with_reducible apply And.intro
  all_goals first
    | (simp only [valid_argv, valid_envp, Fs.valid_fs, valid_creds, valid_id,
        valid_nofile, valid_sigmask, valid_hwcap]
       set_option maxRecDepth 32768 in decide)
    | rfl
    | -- `Fs.fs_keys_relative` on the fixture's empty image; a bounded ∀ over
      -- a `match`-defined Prop, so `decide` finds no instance for it.
      (unfold Fs.fs_keys_relative; intro pf hpf; cases hpf)
    | exact stream_of_list_then_infinite _ _ default_urandom_infinite
    | fail "valid_fin_input: a clause matched none of the shapes"

/-- Blocking SIGKILL makes this launch fail its signal-mask clause.
model: the sigmask clause read back by `Run.valid_input_sigmask`; `Run.valid_sigmask` carries the kernel reading. -/
theorem launch_blocking_sigkill_is_refused :
    ¬ valid_fin_input { launch with fin_sigmask := Z_to_bv 64 0x100 } := by
  intro h
  exact absurd (valid_input_sigmask _ h) (by unfold valid_sigmask; decide)

/-- inherited-divergence: bugs/fin-record-not-injective-on-the-random-field.md --
Two distinct records denote one launch, as the bugs entry records.
model: `to_proc_input` pads `fin_urandom` with `State.default_urandom`, a `stream_const` of the zero byte, so `[0]` and `[]` pad to one stream. -/
theorem padding_byte_denotes_the_empty_declaration :
    { inhabited_fin_input with fin_urandom := [Z_to_bv 8 0] } ≠ inhabited_fin_input
    ∧ to_proc_input { inhabited_fin_input with fin_urandom := [Z_to_bv 8 0] } =
      to_proc_input inhabited_fin_input := by
  constructor
  · intro h
    have hr := congrArg FinProcInput.fin_urandom h
    exact absurd hr (by decide)
  · dsimp only [to_proc_input, inhabited_fin_input, stream_of_list_then]
    unfold default_urandom
    have hz := all_zeros_unfold
    dsimp only [all_zeros] at hz
    rw [← hz]

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.FinInput
