import LinuxProcessSemantics.LinuxProcessSem.StreamLaws

/-! # Checks.Cases.StreamLaws — the stream laws at concrete inputs

Not part of the trusted specification.  `StreamLaws.lean` is the proof
interface of the indexed stream representation: the twins of the Rocq
stream lemmas, and the laws of the Lean encoding that the port's proofs
read streams through (those have no Rocq twin and stand there as the
registered helpers of the day branch's placement guard).  The tests here
are neither.  Each is one of those laws at a concrete input, or a
refutation at one: the two positive instances say what `stream_take`
delivers and leaves on a finite input, asked for more than it holds and
asked for less; the three refutations refuse the answer a wrong
`stream_take`, or a wrong representation of end of input, would give -- a
remainder that forgets the byte a take did not deliver, a delivery that
repeats a byte the input never held, an input that ends and then resumes
-- and the network twin refuses a `NetStream` value that holds a FIN cell
and then a reset cell.
They were written with the laws (PR #692) and sat beside them; the
placement rule of docs/lean-port/BRIEF.md section 13 -- pins under
`Checks/Cases/`, only twins of Rocq lemmas beside the definitions -- is
why they are here and not there.  They moved unchanged, the two positive
instances ahead of the refutations that rewrite with them.  What stays
behind in `StreamLaws.lean` besides the laws is the unbounded fixture
pair `stream_repeat` / `net_stream_repeat` and the five theorems about
them, consumed by nothing else; the day branch's placement guard
registers them as misplaced pins awaiting a follow-up that moves them.

WHAT THE EVIDENCE LINES SAY.  Every claim below is a claim about the Lean
encoding -- `stream_take`, `InputStream` and `NetStream` are the model's
own, defined in `State/Streams.lean`, and no kernel line decides what a
Lean structure can hold or what a Lean function computes -- so each
carries `model:` and cites nothing.  The kernel-facing pins on the same
operations, what a read of standard input or of a peer's script may
deliver with the kernel function beside each, are the ticket A9 section
of `Checks/Cases/State.lean`; the `read` argument lives there.  One half
has no kernel pin anywhere, and cannot have one: that standard input,
once at end of input, stays there is not a behaviour of Linux (a FIFO
gains a writer whenever fs/pipe.c `fifo_open` (Linux v6.18.46) admits
one; a regular file can grow) but the model's premise
about the run's fixture -- Rocq's `InputStream` comment in
`theories/LinuxProcessSem/State.v` says EOF is sticky by construction --
stated as the Rocq worked cases `read_after_eof_deterministic` and
`read_eof_is_sticky` in `theories/LinuxProcessSem/Checks/Cases/Fs/ReadWrite.v`
and exercised under the tracer by the channel cases of
`testing/syscall-check/tests/read_spec.c`.  The A9 section does pin the
network side, where the kernel decides it: `fin_reads_zero_forever` and
`fin_then_byte_rejected`.  The laws the refutations go through --
`ICons_ne_IEof`, `eof_cannot_resume`, `network_terminal_cannot_change`
and the take equations -- stay in `StreamLaws.lean`, and this file reads
them through its import. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.StreamLaws

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State

/-! ## Standard input: a finite input under `stream_take` -/

/-- `stream_take` asked for two bytes of a one-byte input delivers the
one byte and leaves end of input, by the take equations
(`stream_take_cons`, `stream_take_eof`).  The positive half of
`invented_byte_rejected`; the kernel-facing pin at the same shape is
`read_short_then_eof` in the A9 section.
model: a closed `stream_take` at a one-byte input, computed by the model's own take equations. -/
theorem finite_delivery_then_eof (b : byte) :
    stream_take (ICons b IEof) 2 = ([b], IEof) := by
  rw [stream_take_cons, stream_take_eof]

/-- `stream_take` asked for one byte of a two-byte input delivers the
first byte and leaves the second in the remainder, by computation.  The
positive half of `dropped_remainder_rejected`; the kernel-facing pin at
the same shape is `read_leaves_unread_tail` in the A9 section.
model: a closed `stream_take` at a two-byte input, decided by `rfl`. -/
theorem finite_prefix_keeps_remainder (b c : byte) :
    stream_take (ICons b (ICons c IEof)) 1 = ([b], ICons c IEof) := rfl

/-- A one-byte take of a two-byte input leaves the second byte where it
was.  `finite_prefix_keeps_remainder` gives the remainder `ICons c IEof`;
the remainder `IEof` -- what a take that forgot the byte it did not
deliver would leave -- is refused because the representation tells the
two apart (`ICons_ne_IEof`).
model: a closed `stream_take` at a two-byte input; the refused remainder is the model's own `IEof`, and no kernel line decides which `InputStream` a Lean take returns. -/
theorem dropped_remainder_rejected (b c : byte) :
    stream_take (ICons b (ICons c IEof)) 1 ≠ ([b], IEof) := by
  rw [finite_prefix_keeps_remainder]
  intro h
  exact ICons_ne_IEof c IEof (congrArg Prod.snd h)

/-- A take asking for two bytes of a one-byte input delivers the one byte
and stops.  `finite_delivery_then_eof` gives `[b]`; the delivery `[b, b]`
-- what a take that padded a short read by repeating the last byte would
return -- is refused on its length alone, so the refutation holds for
every `b`.
model: a closed `stream_take` at a one-byte input; the refused delivery has the wrong length under the model's own `stream_take`. -/
theorem invented_byte_rejected (b : byte) :
    (stream_take (ICons b IEof) 2).1 ≠ [b, b] := by
  rw [finite_delivery_then_eof]
  intro h
  have hlen := congrArg List.length h
  simp only [List.length_cons, List.length_nil] at hlen
  omega

/-- No `InputStream` ends and then resumes: an input with no byte at index
0 and a byte at index 1 is not a value of the type.  `sticky`
(`State/Streams.lean`) carries a `none` to the next index and
`eof_cannot_resume` to every later one; the statement quantifies over
the stream, so it refuses the shape rather than one fixture.
model: a consequence of the `InputStream` structure's `sticky` field, which encodes the model's premise that the run's standard input does not resume after end of input (Rocq's `InputStream` comment in `theories/LinuxProcessSem/State.v`; the worked cases `read_after_eof_deterministic` / `read_eof_is_sticky` in `theories/LinuxProcessSem/Checks/Cases/Fs/ReadWrite.v`); no kernel line decides it and the A9 section has no stdin pin for it. -/
theorem resumed_terminal_rejected (b : byte) :
    ¬ ∃ s : InputStream, s.byte_at 0 = none ∧ s.byte_at 1 = some b := by
  rintro ⟨s, h0, h1⟩
  exact eof_cannot_resume s 0 1 b (by omega) h0 h1

/-! ## A peer's script: the terminal cells -/

/-- No `NetStream` value holds a FIN and then a reset: a `.NFin` cell at
index 0 followed by a `.NRst` cell at index 1 is not a value of the
type, because `sticky` (`State/Streams.lean`) carries a terminal cell to
the next index unchanged and `network_terminal_cannot_change` to every
later one (that law covers any pair of distinct terminals; this pin
states the FIN-then-RST instance).  The network twin of
`resumed_terminal_rejected`; like it,
stated over an arbitrary stream, so it refuses the shape rather than one
fixture.
model: a consequence of the `NetStream` structure's `sticky` field; that Linux reads keep answering 0 after a FIN, whatever the peer sends next, is the A9 pin `fin_reads_zero_forever` in `Checks/Cases/State.lean`, whose docstring carries the kernel argument. -/
theorem network_fin_cannot_become_reset :
    ¬ ∃ s : NetStream, s.cell_at 0 = .NFin ∧ s.cell_at 1 = .NRst := by
  rintro ⟨s, h0, h1⟩
  have h := network_terminal_cannot_change s 0 1 (by omega) (by rw [h0]; rfl)
  rw [h0, h1] at h
  cases h

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.StreamLaws
