import LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! rocq-baseline: 7b4cf49586658ecbffbab14145ab0969272a0b23 -/

/-! # LinuxProcessSem.State.Streams — standard input and the network

One part of `State.v`'s twin, re-exported by `State.lean`, whose header
says how the ten parts divide the Rocq file, what a part may hold and
where the pins live.

WHAT GOES HERE: the run's byte stream `InputStream`, the network the
environment offers (`NetStream`, `NetQueue`, `PeerAddr`), and the
take operations over both that ticket A9 ported.

Coinductive data. Lean 4.30 supports coinductive predicates in `Prop`;
the Rocq streams here are data in `Type`. `InputStream`, `NetStream`
and `NetQueue` use indexed observations (`Nat → …`). The two types
with terminals carry stickiness proofs, so input cannot resume after
EOF and a network terminal cannot change. `StreamLaws.lean` proves
constructor decomposition and observation laws for this representation.
Those laws do not establish equality with raw Rocq colist values or
a checked translation between the proof assistants. The Rocq constructor
names are retained as definitions. See `lean/README.md`.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.State

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! ## Standard input: the run's byte stream

Rocq: `CoInductive InputStream := IEof | ICons (b : byte) (rest : InputStream)`. -/

structure InputStream where
  /-- The byte at index `i`, or `none` from the end of input on. -/
  byte_at : Nat → Option byte
  /-- The end of input is final. -/
  sticky : ∀ i, byte_at i = none → byte_at (i + 1) = none

def IEof : InputStream := ⟨fun _ => none, fun _ _ => rfl⟩
def ICons (b : byte) (rest : InputStream) : InputStream :=
  ⟨fun i => match i with | 0 => some b | i' + 1 => rest.byte_at i',
   by
     intro i h
     cases i with
     | zero => exact absurd h (by simp)
     | succ i' => exact rest.sticky i' h⟩

/-- The head/tail view a Rocq `match s with IEof => … | ICons b r => …` takes. -/
def InputStream.uncons (s : InputStream) : Option (byte × InputStream) :=
  match s.byte_at 0 with
  | none => none
  | some b => some (b, ⟨fun i => s.byte_at (i + 1), fun i h => s.sticky (i + 1) h⟩)

/-- Take up to `k` bytes off the front of `s`: the bytes actually available
together with the REMAINING stream (`IEof` once the input ran out, as in
Rocq). -/
def stream_take (s : InputStream) (k : Nat) : List byte × InputStream :=
  match k with
  | 0 => ([], s)
  | k' + 1 =>
    match s.uncons with
    | none => ([], IEof)
    | some (b, rest) =>
      let (bs, rest') := stream_take rest k'
      (b :: bs, rest')

/-! ## A stream that never ends

Mirrors `theories/LinuxProcessSem/State.v`'s `stream_infinite`,
`stream_const` and `default_urandom`.

WHERE THE TWO REPRESENTATIONS PART.  Rocq's predicate is COINDUCTIVE,
because a `CoInductive InputStream` offers nothing else: a derivation
that never reaches `IEof` has to be a productive corecursion.  Here the
stream IS an indexed observation, so "never ends" is the direct
statement that every index carries a byte, and it needs no coinduction
at all.  The two say the same thing about the same object; what differs
is the representation, as it does for `InputStream` itself. -/

/-- The declared stream never reaches end of input: every index carries a
byte.  Rocq `stream_infinite`. -/
def stream_infinite (s : InputStream) : Prop := ∀ i, (s.byte_at i).isSome

theorem stream_infinite_not_eof : ¬ stream_infinite IEof := by
  intro h
  have := h 0
  simp [IEof] at this

/-- The constant stream, the witness that the predicate is inhabited and
the one a fixture declares.  Rocq `stream_const`. -/
def stream_const (b : byte) : InputStream :=
  ⟨fun _ => some b, fun _ h => absurd h (by simp)⟩

theorem stream_const_infinite (b : byte) : stream_infinite (stream_const b) := by
  intro _; simp [stream_const]

/-- THE RANDOM STREAM A FIXTURE GETS WHEN IT DOES NOT SAY: zero bytes
forever.  A FIXTURE DEFAULT, in no theorem, and it is what
`ProcInput.mkProcInput` fills `in_urandom` with.  It used to be `IEof`,
and could not stay: `Run.valid_urandom` asks that a launch's declared
random stream never end, so a fixture built with `IEof` would fail its
own validity pin.  Rocq `default_urandom`.

`@[irreducible]` IS LOAD-BEARING FOR THE BUILD, and it is a fact about
Lean's `simp` rather than about the definition.  Once `fixture_of`'s
random slot stopped being the trivial `IEof`, six `sys_norm` pins in
`Checks/Cases/Fs/ReadWrite.lean` hit `maximum recursion depth` unfolding
this through the model term.  Nothing needs it to compute: every
`/dev/urandom` pin closes by `rfl` or by `IEof_ne_ICons`, and the two
`rwx_flag_ns` validity witnesses name it in their `simp` list where they
do need to see through it.  Rocq's `State.default_urandom` carries no
`Opaque` or `Strategy` counterpart, so the twin mirrors the DEFINITION
and not its reduction behaviour. -/
@[irreducible] def default_urandom : InputStream := stream_const (Z_to_bv 8 0)

theorem default_urandom_infinite : stream_infinite default_urandom := by
  unfold default_urandom; exact stream_const_infinite _

/-! ## The network the environment offers

Rocq: `CoInductive NetStream := NFin | NRst | NTimedOut | NCons b rest` and
`CoInductive NetQueue := NConn peer script rest` (infinite, no nil). -/

inductive NetCell : Type
  | NFin | NRst | NTimedOut
  | NByte (b : byte)

/-- The three terminals; a script that reached one stays there. -/
def NetCell.isTerminal : NetCell → Bool
  | .NByte _ => false
  | _ => true

structure NetStream where
  cell_at : Nat → NetCell
  /-- A terminal is final. -/
  sticky : ∀ i, (cell_at i).isTerminal = true → cell_at (i + 1) = cell_at i

def NFin : NetStream := ⟨fun _ => .NFin, fun _ _ => rfl⟩
def NRst : NetStream := ⟨fun _ => .NRst, fun _ _ => rfl⟩
def NTimedOut : NetStream := ⟨fun _ => .NTimedOut, fun _ _ => rfl⟩
def NCons (b : byte) (rest : NetStream) : NetStream :=
  ⟨fun i => match i with | 0 => .NByte b | i' + 1 => rest.cell_at i',
   by
     intro i h
     cases i with
     | zero => exact absurd h (by simp [NetCell.isTerminal])
     | succ i' => exact rest.sticky i' h⟩

structure PeerAddr where
  mkPeer ::
  pa_addr : BitVec 32   -- sin_addr.s_addr, network order
  pa_port : BitVec 16   -- sin_port, network order

/-- INFINITE, with no terminal (Rocq: no nil constructor), so no
stickiness field: every function is a queue Rocq can write. -/
structure NetQueue where
  conn_at : Nat → PeerAddr × NetStream

def NConn (peer : PeerAddr) (script : NetStream) (rest : NetQueue) : NetQueue :=
  ⟨fun i => match i with | 0 => (peer, script) | i' + 1 => rest.conn_at i'⟩

/-- THE QUIET ENVIRONMENT: connection after connection from 0.0.0.0:0 with
nothing to say. -/
def net_silent : NetQueue :=
  ⟨fun _ => (PeerAddr.mkPeer (Z_to_bv 32 0) (Z_to_bv 16 0), NFin)⟩

def nq_peer (q : NetQueue) : PeerAddr := (q.conn_at 0).1
def nq_script (q : NetQueue) : NetStream := (q.conn_at 0).2
def nq_rest (q : NetQueue) : NetQueue := ⟨fun i => q.conn_at (i + 1)⟩

/-! ## Ticket A9: stream operations over the encoded streams

Mirrors `theories/LinuxProcessSem/State.v` `stream_bytes` … `stream_take_z`
and `net_take` … `net_take_z` at the rocq-baseline commit, definition for
definition.  The Rocq bodies match a colist constructor; the Lean twins
match the head observation through `InputStream.uncons` and its
`NetStream` analogue below, which is the only representational difference.
The laws these obey are in `StreamLaws.lean`; the kernel-pinned tests are
the section "Stream and network reads — ticket A9" of
`Checks/Cases/State.lean`. -/

/-- The bytes a read of at most `k` delivers (Rocq `stream_bytes`). -/
def stream_bytes (s : InputStream) (k : Nat) : List byte := (stream_take s k).1

/-- What is left after such a read (Rocq `stream_rest`). -/
def stream_rest (s : InputStream) (k : Nat) : InputStream := (stream_take s k).2

/-- `stream_take` indexed by a binary positive (Rocq `stream_take_pos`), for
the one place the count is the kernel's aggregate rather than the length of
a delivered list: the bytes the source could supply to a read of `n`, which
can be `MAX_RW_COUNT` (fs/read_write.c `vfs_read` clamps `count` to it,
Linux v6.18.46, commit 1f99e9ab748f).  Recursing on the binary digits of
the count costs the bytes actually taken plus one step per digit, so an
executable checker never builds a unary numeral of that size; the Rocq
docstring carries the full argument.  `StreamLaws.stream_take_pos_eq` says
it computes exactly `stream_take` at `p.toNat`.  Where Rocq matches the
remainder against `IEof`, this matches its `uncons` against `none`. -/
def stream_take_pos (s : InputStream) : positive → List byte × InputStream
  | xH => stream_take s 1
  | xO p' =>
      let r1 := stream_take_pos s p'
      match r1.2.uncons with
      | none => (r1.1, IEof)
      | some _ =>
          let r2 := stream_take_pos r1.2 p'
          (r1.1 ++ r2.1, r2.2)
  | xI p' =>
      let r1 := stream_take_pos s p'
      match r1.2.uncons with
      | none => (r1.1, IEof)
      | some _ =>
          let r2 := stream_take_pos r1.2 p'
          match r2.2.uncons with
          | none => (r1.1 ++ r2.1, IEof)
          | some _ =>
              let r3 := stream_take r2.2 1
              (r1.1 ++ r2.1 ++ r3.1, r3.2)

/-- Rocq `stream_take_z`: `match n with Zpos p => stream_take_pos s p | _ =>
([], s)`.  Lean's `Int` has no positive constructor, so the `Zpos` arm is
spelled through `positive.ofNat` (the Prelude's `Z.to_pos`) on `n.toNat`,
guarded by `0 < n`; `StreamLaws.stream_take_z_eq` recovers Rocq's
`stream_take s (Z.to_nat n)` reading. -/
def stream_take_z (s : InputStream) (n : Int) : List byte × InputStream :=
  if 0 < n then stream_take_pos s (positive.ofNat n.toNat) else ([], s)

/-- The head/tail view a Rocq `match s with NCons b r => … | _ => …` takes:
`none` at any of the three terminals.  Not a Rocq definition; the
`NetStream` analogue of `InputStream.uncons`. -/
def NetStream.uncons (s : NetStream) : Option (byte × NetStream) :=
  match s.cell_at 0 with
  | .NByte b => some (b, ⟨fun i => s.cell_at (i + 1), fun i h => s.sticky (i + 1) h⟩)
  | _ => none

/-- Take up to `k` bytes off the front of a connection's script (Rocq
`net_take`): the bytes actually available, fewer than `k` when a terminal
comes first, together with the REMAINING script.  A terminal is left in
place rather than consumed because the kernel's is: `tcp_fin`
(net/ipv4/tcp_input.c, Linux v6.18.46, commit 1f99e9ab748f) sets
`RCV_SHUTDOWN` and `SOCK_DONE`.  The connected sockets a modeled run
holds are the ones `accept` handed out, `SS_CONNECTED` since
`__inet_accept` (net/ipv4/af_inet.c, Linux v6.18.46) — `connect_spec`
(Sys/Net/Socket.v) never produces one by connecting — and on such a
socket the one syscall path that clears the flags is a `connect` with
`AF_UNSPEC`, which `__inet_stream_connect` (net/ipv4/af_inet.c, Linux
v6.18.46) hands to `tcp_disconnect` (net/ipv4/tcp.c, same version)
before it looks at the socket's state; every other `connect` on it is
`-EISCONN` there, so `tcp_connect_init` (net/ipv4/tcp_output.c, Linux
v6.18.46) cannot run, and `__tcp_close` (net/ipv4/tcp.c, same version)
calls `tcp_disconnect` only on the last release, which no read follows.
`connect_spec` declines the `AF_UNSPEC` `connect` on a connected socket,
so every later read finds the terminal again; this stops holding the day
that arm is modeled. -/
def net_take (s : NetStream) (k : Nat) : List byte × NetStream :=
  match k with
  | 0 => ([], s)
  | k' + 1 =>
    match s.uncons with
    | some (b, rest) =>
      let r := net_take rest k'
      (b :: r.1, r.2)
    | none => ([], s)

/-- The bytes a read of at most `k` delivers (Rocq `net_bytes`). -/
def net_bytes (s : NetStream) (k : Nat) : List byte := (net_take s k).1

/-- What is left after such a read (Rocq `net_rest`). -/
def net_rest (s : NetStream) (k : Nat) : NetStream := (net_take s k).2

/-- Rocq `net_ended`.  Exists so that `net_take_pos` can stop at a terminal
with one Bool test per digit, where `stream_take_pos` matches the
remainder instead; `StreamLaws.net_take_ended` is the law it is used for. -/
def net_ended (s : NetStream) : Bool :=
  match s.cell_at 0 with
  | .NByte _ => false
  | _ => true

/-- The `NetStream` half of `stream_take_pos` (Rocq `net_take_pos`); see
that for why the digit-indexed take exists.  `StreamLaws.net_take_pos_eq`
says it computes exactly `net_take` at `p.toNat`. -/
def net_take_pos (s : NetStream) : positive → List byte × NetStream
  | xH => net_take s 1
  | xO p' =>
      let r1 := net_take_pos s p'
      if net_ended r1.2 then r1
      else
        let r2 := net_take_pos r1.2 p'
        (r1.1 ++ r2.1, r2.2)
  | xI p' =>
      let r1 := net_take_pos s p'
      if net_ended r1.2 then r1
      else
        let r2 := net_take_pos r1.2 p'
        if net_ended r2.2 then (r1.1 ++ r2.1, r2.2)
        else
          let r3 := net_take r2.2 1
          (r1.1 ++ r2.1 ++ r3.1, r3.2)

/-- Rocq `net_take_z`, spelled as `stream_take_z` is. -/
def net_take_z (s : NetStream) (n : Int) : List byte × NetStream :=
  if 0 < n then net_take_pos s (positive.ofNat n.toNat) else ([], s)

end LinuxProcessSemantics.LinuxProcessSem.State
