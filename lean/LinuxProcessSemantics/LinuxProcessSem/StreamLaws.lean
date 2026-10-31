import LinuxProcessSemantics.LinuxProcessSem.State

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! Proof interface for the indexed stream representation.

The input operation laws mirror the `InputStream` section of
`theories/LinuxProcessSem/State.v` (`stream_take` … `stream_take_z`) and the
network constructors its `NetStream` and `NetQueue` sections, read at the
rocq-baseline commit above.  That header line has the shape
`tools/check_lean_spec_parity.py` reads, but the tool does not read this
file (its scope is `Sys/` and the twins its `ROCQ_EXTRA` table names), so
the baseline is kept by hand — `tools/check_lean_test_monotonic.py` reads
the line only to refuse a move backwards in Rocq history; the sections
are cited by name because their line numbers move (at 9a070af9, where
this note was first written, the `InputStream` section began at
`State.v:1454`, `stream_take` stood at :1467 and its laws ran from :1485;
at the baseline they stand elsewhere).
The decomposition law supplies the case analysis that Rocq obtains from
the colist constructors. These are laws of the existing Lean representation;
they do not assert equality of raw Rocq coinductive values with functions.
No finiteness condition is imposed on an input or a network queue. -/

namespace LinuxProcessSemantics.LinuxProcessSem.State

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase

theorem InputStream.ext {s t : InputStream}
    (h : ∀ i, s.byte_at i = t.byte_at i) : s = t := by
  cases s with
  | mk f hf =>
      cases t with
      | mk g hg =>
          have hfg : f = g := funext h
          cases hfg
          rfl

theorem InputStream.none_add (s : InputStream) (i k : Nat)
    (h : s.byte_at i = none) : s.byte_at (i + k) = none := by
  induction k with
  | zero => exact h
  | succ k ih => exact s.sticky (i + k) ih

theorem InputStream.none_of_le (s : InputStream) {i j : Nat}
    (hij : i ≤ j) (h : s.byte_at i = none) : s.byte_at j = none := by
  have hsum : i + (j - i) = j := by omega
  rw [← hsum]
  exact s.none_add i (j - i) h

theorem InputStream.eq_eof_of_head_none (s : InputStream)
    (h : s.byte_at 0 = none) : s = IEof := by
  apply InputStream.ext
  intro i
  simpa only [Nat.zero_add, IEof] using s.none_add 0 i h

@[simp] theorem uncons_eof : InputStream.uncons IEof = none := rfl

@[simp] theorem uncons_cons (b : byte) (s : InputStream) :
    InputStream.uncons (ICons b s) = some (b, s) := rfl

theorem stream_decompose (s : InputStream) :
    s = match s.uncons with
      | none => IEof
      | some (b, r) => ICons b r := by
  cases h : s.byte_at 0 with
  | none =>
      simp only [InputStream.uncons, h]
      exact s.eq_eof_of_head_none h
  | some b =>
      simp only [InputStream.uncons, h]
      apply InputStream.ext
      intro i
      cases i with
      | zero => exact h
      | succ i => rfl

@[simp] theorem uncons_eq_none_iff (s : InputStream) : s.uncons = none ↔ s = IEof := by
  constructor
  · intro h
    have hs := stream_decompose s
    simpa only [h] using hs
  · rintro rfl
    rfl

@[simp] theorem uncons_eq_some_iff (s : InputStream) (b : byte) (r : InputStream) :
    s.uncons = some (b, r) ↔ s = ICons b r := by
  constructor
  · intro h
    have hs := stream_decompose s
    simpa only [h] using hs
  · rintro rfl
    exact uncons_cons b r

theorem stream_cases (s : InputStream) : s = IEof ∨ ∃ b r, s = ICons b r := by
  cases h : s.uncons with
  | none => exact Or.inl ((uncons_eq_none_iff s).mp h)
  | some p => exact Or.inr ⟨p.1, p.2, (uncons_eq_some_iff s p.1 p.2).mp h⟩

@[simp] theorem ICons_eq_ICons (b b' : byte) (s s' : InputStream) :
    ICons b s = ICons b' s' ↔ b = b' ∧ s = s' := by
  constructor
  · intro h
    have hu := congrArg InputStream.uncons h
    simpa only [uncons_cons, Option.some.injEq, Prod.mk.injEq] using hu
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem ICons_ne_IEof (b : byte) (s : InputStream) : ICons b s ≠ IEof := by
  intro h
  have hu := congrArg InputStream.uncons h
  simp only [uncons_cons, uncons_eof] at hu
  cases hu

@[simp] theorem IEof_ne_ICons (b : byte) (s : InputStream) : IEof ≠ ICons b s :=
  Ne.symm (ICons_ne_IEof b s)

@[simp] theorem stream_take_zero (s : InputStream) : stream_take s 0 = ([], s) := rfl

@[simp] theorem stream_take_eof (k : Nat) : stream_take IEof k = ([], IEof) := by
  cases k <;> rfl

@[simp] theorem stream_take_nil_of_eof (k : Nat) : (stream_take IEof k).1 = [] := by
  rw [stream_take_eof]

theorem stream_take_cons (b : byte) (s : InputStream) (k : Nat) :
    stream_take (ICons b s) (k + 1) =
      (b :: (stream_take s k).1, (stream_take s k).2) := by
  simp only [stream_take, uncons_cons]

theorem stream_take_length (k : Nat) (s : InputStream) : (stream_take s k).1.length ≤ k := by
  induction k generalizing s with
  | zero => simp only [stream_take_zero, List.length_nil, Nat.le_refl]
  | succ k ih =>
      rcases stream_cases s with rfl | ⟨b, r, rfl⟩
      · simp only [stream_take_eof, List.length_nil, Nat.zero_le]
      · rw [stream_take_cons]
        exact Nat.succ_le_succ (ih r)

theorem stream_take_bytes_self (k : Nat) (s : InputStream) :
    (stream_take s (stream_take s k).1.length).1 = (stream_take s k).1 := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rcases stream_cases s with rfl | ⟨b, r, rfl⟩
      · simp only [stream_take_eof]
      · simp only [stream_take_cons, List.length_cons, ih]

theorem stream_take_rest_self (k : Nat) (s : InputStream) :
    (stream_take s (stream_take s k).1.length).2 = (stream_take s k).2 := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rcases stream_cases s with rfl | ⟨b, r, rfl⟩
      · simp only [stream_take_eof]
      · simp only [stream_take_cons, List.length_cons, ih]

theorem stream_take_add (a b : Nat) (s : InputStream) :
    stream_take s (a + b) =
      ((stream_take s a).1 ++ (stream_take (stream_take s a).2 b).1,
       (stream_take (stream_take s a).2 b).2) := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add, stream_take_zero, List.nil_append]
  | succ a ih =>
      rcases stream_cases s with rfl | ⟨c, r, rfl⟩
      · simp only [stream_take_eof, List.nil_append]
      · simp only [Nat.succ_add, stream_take_cons, ih, List.cons_append]

/-- A bounded read agrees at every delivered position with the indexed
observation. This also fixes the result at positions after EOF. -/
theorem stream_take_getElem? (s : InputStream) (k i : Nat) (hi : i < k) :
    (stream_take s k).1[i]? = s.byte_at i := by
  induction k generalizing s i with
  | zero => omega
  | succ k ih =>
      rcases stream_cases s with rfl | ⟨b, r, rfl⟩
      · rw [stream_take_eof]
        exact List.getElem?_nil
      · cases i with
        | zero => rw [stream_take_cons]; rfl
        | succ i =>
            rw [stream_take_cons]
            exact ih r i (by omega)

/-- The remainder is shifted by the requested count, including when the
read ends early: all observations after EOF are still EOF. -/
theorem stream_take_rest_at (s : InputStream) (k i : Nat) :
    (stream_take s k).2.byte_at i = s.byte_at (k + i) := by
  induction k generalizing s with
  | zero => simp only [stream_take_zero, Nat.zero_add]
  | succ k ih =>
      rcases stream_cases s with rfl | ⟨b, r, rfl⟩
      · rfl
      · rw [stream_take_cons]
        simpa only [Nat.succ_add, ICons] using ih r

/-- Finite byte observations determine this Lean representation. This is
not a theorem equating arbitrary raw Rocq colists. -/
theorem stream_eq_of_all_prefixes (s t : InputStream)
    (h : ∀ k, (stream_take s k).1 = (stream_take t k).1) : s = t := by
  apply InputStream.ext
  intro i
  rw [← stream_take_getElem? s (i + 1) i (by omega),
      ← stream_take_getElem? t (i + 1) i (by omega)]
  exact congrArg (fun bs : List byte => bs[i]?) (h (i + 1))

theorem eof_cannot_resume (s : InputStream) (i j : Nat) (b : byte)
    (hij : i ≤ j) (heof : s.byte_at i = none) : s.byte_at j ≠ some b := by
  rw [s.none_of_le hij heof]
  intro h
  cases h

/- A genuinely unbounded input: data defined at every index, not a finite
fixture with a large observation limit.  The finite side of the domain is
exercised by the tests in `Checks/Cases/StreamLaws.lean`. -/
def stream_repeat (b : byte) : InputStream :=
  ⟨fun _ => some b, by intro _ h; cases h⟩

theorem stream_repeat_unfold (b : byte) : stream_repeat b = ICons b (stream_repeat b) := by
  apply InputStream.ext
  intro i
  cases i <;> rfl

theorem stream_repeat_take (b : byte) (k : Nat) :
    stream_take (stream_repeat b) k = (List.replicate k b, stream_repeat b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [stream_repeat_unfold b, stream_take_cons]
      rw [← stream_repeat_unfold b, ih]
      rfl

theorem stream_repeat_ne_eof (b : byte) : stream_repeat b ≠ IEof := by
  rw [stream_repeat_unfold]
  exact ICons_ne_IEof _ _

theorem NetStream.ext {s t : NetStream}
    (h : ∀ i, s.cell_at i = t.cell_at i) : s = t := by
  cases s with
  | mk f hf =>
      cases t with
      | mk g hg =>
          have hfg : f = g := funext h
          cases hfg
          rfl

theorem NetStream.terminal_add (s : NetStream) (i k : Nat)
    (h : (s.cell_at i).isTerminal = true) : s.cell_at (i + k) = s.cell_at i := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk : (s.cell_at (i + k)).isTerminal = true := by rw [ih]; exact h
      exact (s.sticky (i + k) hk).trans ih

theorem NetStream.eq_of_terminal_head (s : NetStream) (c : NetCell)
    (hc : c.isTerminal = true) (h : s.cell_at 0 = c) :
    ∀ i, s.cell_at i = c := by
  intro i
  have hterm : (s.cell_at 0).isTerminal = true := by rw [h]; exact hc
  simpa only [Nat.zero_add] using (s.terminal_add 0 i hterm).trans h

theorem network_cases (s : NetStream) :
    s = NFin ∨ s = NRst ∨ s = NTimedOut ∨ ∃ b r, s = NCons b r := by
  cases h : s.cell_at 0 with
  | NFin =>
      exact Or.inl (NetStream.ext (s.eq_of_terminal_head .NFin rfl h))
  | NRst =>
      exact Or.inr (Or.inl (NetStream.ext (s.eq_of_terminal_head .NRst rfl h)))
  | NTimedOut =>
      exact Or.inr (Or.inr (Or.inl
        (NetStream.ext (s.eq_of_terminal_head .NTimedOut rfl h))))
  | NByte b =>
      let r : NetStream :=
        ⟨fun i => s.cell_at (i + 1), fun i ht => s.sticky (i + 1) ht⟩
      refine Or.inr (Or.inr (Or.inr ⟨b, r, ?_⟩))
      apply NetStream.ext
      intro i
      cases i with
      | zero => exact h
      | succ i => rfl

theorem NCons_eq_NCons (b b' : byte) (s s' : NetStream) :
    NCons b s = NCons b' s' ↔ b = b' ∧ s = s' := by
  constructor
  · intro h
    have hb := congrArg (fun q : NetStream => q.cell_at 0) h
    have hs : s = s' := NetStream.ext (fun i =>
      congrArg (fun q : NetStream => q.cell_at (i + 1)) h)
    exact ⟨NetCell.NByte.inj hb, hs⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem network_terminal_cannot_change (s : NetStream) (i j : Nat)
    (hij : i ≤ j) (h : (s.cell_at i).isTerminal = true) : s.cell_at j = s.cell_at i := by
  have hsum : i + (j - i) = j := by omega
  rw [← hsum]
  exact s.terminal_add i (j - i) h

theorem network_fin_ne_reset : NFin ≠ NRst := by
  intro h
  have h0 := congrArg (fun s : NetStream => s.cell_at 0) h
  cases h0

theorem network_fin_ne_timeout : NFin ≠ NTimedOut := by
  intro h
  have h0 := congrArg (fun s : NetStream => s.cell_at 0) h
  cases h0

theorem network_reset_ne_timeout : NRst ≠ NTimedOut := by
  intro h
  have h0 := congrArg (fun s : NetStream => s.cell_at 0) h
  cases h0

theorem network_fin_stays_fin (i : Nat) : NFin.cell_at i = .NFin := rfl
theorem network_reset_stays_reset (i : Nat) : NRst.cell_at i = .NRst := rfl
theorem network_timeout_stays_timeout (i : Nat) : NTimedOut.cell_at i = .NTimedOut := rfl

def net_stream_repeat (b : byte) : NetStream :=
  ⟨fun _ => .NByte b, by intro _ h; cases h⟩

theorem net_stream_repeat_unfold (b : byte) :
    net_stream_repeat b = NCons b (net_stream_repeat b) := by
  apply NetStream.ext
  intro i
  cases i <;> rfl

theorem network_byte_is_not_terminal (b : byte) (i : Nat) :
    ((net_stream_repeat b).cell_at i).isTerminal = false := rfl

theorem NetQueue.ext {q r : NetQueue} (h : ∀ i, q.conn_at i = r.conn_at i) : q = r := by
  cases q with
  | mk f =>
      cases r with
      | mk g => exact congrArg NetQueue.mk (funext h)

@[simp] theorem nq_peer_cons (peer : PeerAddr) (script : NetStream) (rest : NetQueue) :
    nq_peer (NConn peer script rest) = peer := rfl

@[simp] theorem nq_script_cons (peer : PeerAddr) (script : NetStream) (rest : NetQueue) :
    nq_script (NConn peer script rest) = script := rfl

@[simp] theorem nq_rest_cons (peer : PeerAddr) (script : NetStream) (rest : NetQueue) :
    nq_rest (NConn peer script rest) = rest := rfl

theorem net_queue_decompose (q : NetQueue) :
    q = NConn (nq_peer q) (nq_script q) (nq_rest q) := by
  apply NetQueue.ext
  intro i
  cases i <;> rfl

theorem silent_queue_unfold :
    net_silent = NConn (PeerAddr.mkPeer 0 0) NFin net_silent := by
  apply NetQueue.ext
  intro i
  cases i <;> rfl

theorem silent_queue_tail : nq_rest net_silent = net_silent := rfl

/-! ## Ticket A9: laws of the take operations

The `net_take` laws mirror `theories/LinuxProcessSem/State.v` `net_take_zero`
… `net_take_z_eq`, and the digit-recursion laws mirror
`stream_take_pos_eq` / `stream_take_z_eq`, at the rocq-baseline commit.
This section cites no kernel source: these are laws of the representation,
and the kernel-pinned tests of the operations are in
`Checks/Cases/State.lean`. -/

@[simp] theorem net_uncons_fin : NetStream.uncons NFin = none := rfl
@[simp] theorem net_uncons_rst : NetStream.uncons NRst = none := rfl
@[simp] theorem net_uncons_timedout : NetStream.uncons NTimedOut = none := rfl
@[simp] theorem net_uncons_cons (b : byte) (s : NetStream) :
    NetStream.uncons (NCons b s) = some (b, s) := rfl

@[simp] theorem net_ended_fin : net_ended NFin = true := rfl
@[simp] theorem net_ended_rst : net_ended NRst = true := rfl
@[simp] theorem net_ended_timedout : net_ended NTimedOut = true := rfl
@[simp] theorem net_ended_cons (b : byte) (s : NetStream) : net_ended (NCons b s) = false := rfl

@[simp] theorem net_take_zero (s : NetStream) : net_take s 0 = ([], s) := rfl

@[simp] theorem net_take_fin (k : Nat) : net_take NFin k = ([], NFin) := by
  cases k <;> rfl

@[simp] theorem net_take_rst (k : Nat) : net_take NRst k = ([], NRst) := by
  cases k <;> rfl

@[simp] theorem net_take_timedout (k : Nat) : net_take NTimedOut k = ([], NTimedOut) := by
  cases k <;> rfl

theorem net_take_cons (b : byte) (s : NetStream) (k : Nat) :
    net_take (NCons b s) (k + 1) =
      (b :: (net_take s k).1, (net_take s k).2) := by
  simp only [net_take, net_uncons_cons]

/-- A read never delivers more than it was asked for. -/
theorem net_take_length (k : Nat) (s : NetStream) : (net_take s k).1.length ≤ k := by
  induction k generalizing s with
  | zero => simp only [net_take_zero, List.length_nil, Nat.le_refl]
  | succ k ih =>
      rcases network_cases s with rfl | rfl | rfl | ⟨b, r, rfl⟩
      · simp only [net_take_fin, List.length_nil, Nat.zero_le]
      · simp only [net_take_rst, List.length_nil, Nat.zero_le]
      · simp only [net_take_timedout, List.length_nil, Nat.zero_le]
      · rw [net_take_cons]
        exact Nat.succ_le_succ (ih r)

theorem net_take_bytes_self (k : Nat) (s : NetStream) :
    (net_take s (net_take s k).1.length).1 = (net_take s k).1 := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rcases network_cases s with rfl | rfl | rfl | ⟨b, r, rfl⟩
      · simp only [net_take_fin]
      · simp only [net_take_rst]
      · simp only [net_take_timedout]
      · simp only [net_take_cons, List.length_cons, ih]

theorem net_take_rest_self (k : Nat) (s : NetStream) :
    (net_take s (net_take s k).1.length).2 = (net_take s k).2 := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rcases network_cases s with rfl | rfl | rfl | ⟨b, r, rfl⟩
      · simp only [net_take_fin]
      · simp only [net_take_rst]
      · simp only [net_take_timedout]
      · simp only [net_take_cons, List.length_cons, ih]

theorem net_take_nil_of_fin (k : Nat) : (net_take NFin k).1 = [] := by
  rw [net_take_fin]
theorem net_take_nil_of_rst (k : Nat) : (net_take NRst k).1 = [] := by
  rw [net_take_rst]
theorem net_take_nil_of_timedout (k : Nat) : (net_take NTimedOut k).1 = [] := by
  rw [net_take_timedout]

theorem net_take_add (a b : Nat) (s : NetStream) :
    net_take s (a + b) =
      ((net_take s a).1 ++ (net_take (net_take s a).2 b).1,
       (net_take (net_take s a).2 b).2) := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add, net_take_zero, List.nil_append]
  | succ a ih =>
      rcases network_cases s with rfl | rfl | rfl | ⟨c, r, rfl⟩
      · simp only [net_take_fin, List.nil_append]
      · simp only [net_take_rst, List.nil_append]
      · simp only [net_take_timedout, List.nil_append]
      · simp only [Nat.succ_add, net_take_cons, ih, List.cons_append]

theorem net_take_ended (s : NetStream) (k : Nat) (h : net_ended s = true) :
    net_take s k = ([], s) := by
  rcases network_cases s with rfl | rfl | rfl | ⟨b, r, rfl⟩
  · exact net_take_fin k
  · exact net_take_rst k
  · exact net_take_timedout k
  · rw [net_ended_cons] at h
    cases h

theorem net_take_pos_eq (p : positive) (s : NetStream) :
    net_take_pos s p = net_take s p.toNat := by
  induction p generalizing s with
  | xH => rfl
  | xO p ih =>
      have h2 : positive.toNat (xO p) = p.toNat + p.toNat := by
        simp only [positive.toNat]
        omega
      simp only [net_take_pos, ih]
      rw [h2, net_take_add]
      cases h1 : net_ended (net_take s p.toNat).2
      · simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [↓reduceIte, net_take_ended _ _ h1, List.append_nil]
  | xI p ih =>
      have h2 : positive.toNat (xI p) = p.toNat + (p.toNat + 1) := by
        simp only [positive.toNat]
        omega
      simp only [net_take_pos, ih]
      rw [h2, net_take_add, net_take_add p.toNat 1]
      cases h1 : net_ended (net_take s p.toNat).2
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases h2 : net_ended (net_take (net_take s p.toNat).2 p.toNat).2
        · simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc]
        · simp only [↓reduceIte, net_take_ended _ _ h2, List.append_nil]
      · simp only [↓reduceIte, net_take_ended _ _ h1, List.append_nil]

theorem net_take_z_eq (s : NetStream) (n : Int) :
    net_take_z s n = net_take s n.toNat := by
  unfold net_take_z
  by_cases h : 0 < n
  · simp only [h, ↓reduceIte]
    rw [net_take_pos_eq, positive.toNat_ofNat n.toNat (by omega)]
  · simp only [h, ↓reduceIte]
    have h0 : n.toNat = 0 := by omega
    rw [h0, net_take_zero]

theorem stream_take_pos_eq (p : positive) (s : InputStream) :
    stream_take_pos s p = stream_take s p.toNat := by
  induction p generalizing s with
  | xH => rfl
  | xO p ih =>
      have h2 : positive.toNat (xO p) = p.toNat + p.toNat := by
        simp only [positive.toNat]
        omega
      simp only [stream_take_pos, ih]
      rw [h2, stream_take_add]
      cases h1 : (stream_take s p.toNat).2.uncons
      · have hE := (uncons_eq_none_iff _).mp h1
        simp only [hE, stream_take_eof, List.append_nil]
      · simp only
  | xI p ih =>
      have h2 : positive.toNat (xI p) = p.toNat + (p.toNat + 1) := by
        simp only [positive.toNat]
        omega
      simp only [stream_take_pos, ih]
      rw [h2, stream_take_add, stream_take_add p.toNat 1]
      cases h1 : (stream_take s p.toNat).2.uncons
      · have hE := (uncons_eq_none_iff _).mp h1
        simp only [hE, stream_take_eof, List.append_nil]
      · simp only
        cases h2 : (stream_take (stream_take s p.toNat).2 p.toNat).2.uncons
        · have hE := (uncons_eq_none_iff _).mp h2
          simp only [hE, stream_take_eof, List.append_nil]
        · simp only [List.append_assoc]

theorem stream_take_z_eq (s : InputStream) (n : Int) :
    stream_take_z s n = stream_take s n.toNat := by
  unfold stream_take_z
  by_cases h : 0 < n
  · simp only [h, ↓reduceIte]
    rw [stream_take_pos_eq, positive.toNat_ofNat n.toNat (by omega)]
  · simp only [h, ↓reduceIte]
    have h0 : n.toNat = 0 := by omega
    rw [h0, stream_take_zero]

end LinuxProcessSemantics.LinuxProcessSem.State
