import LinuxProcessSemantics.LinuxProcessSem.Monad
import LinuxProcessSemantics.LinuxProcessSem.StreamLaws

/-! # Checks.Cases.Monad — pins on the `Monad` setters and readings

Pins for the ticket A11 twin in `LinuxProcessSem/Monad.lean`,
`set_utsname`, for the ticket A12 twins `set_statpin`,
`set_sigaltstack_installed`, `set_sigabrt_pending` and `set_killed`, and,
in the ticket D4 section, for the readings of `bind` at each primitive.
Not part of the trusted specification: this file is QA on the
definitions, written to be READ.  Every pin carries an evidence line
(`tools/check_lean_pin_evidence.py`): `model:` where it checks the
monad's own vocabulary, and `kernel:` where a setter's pin rests on what
the kernel does at the call that writes it. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Monad

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad

/-- The setter's one admissible outcome: no events, the pin written.
model: `set_utsname` is `modify (with_utsname bs)`, read at its one outcome; no kernel claim. -/
theorem set_utsname_ok (bs : List byte) (i : SyscallInput) (m : Model) :
    set_utsname bs i m (Ok () (with_utsname bs m) []) := rfl

/-- Pinning the name is not a place the model leaves its surface: Rocq's
`uname_spec` (Sys/Kernel/Sys.v at f44244ad, the caller once ported)
declines only the partial-copy case, a `copy_to_user` that faults
part-way, never the write of the pin.
model: a `modify` admits no `Unmodeled`; which calls write the pin is `uname_spec`'s business, not the setter's. -/
theorem set_utsname_not_unmodeled (bs : List byte) (i : SyscallInput) (m : Model) :
    ¬ set_utsname bs i m Unmodeled := fun h => nomatch h

/-- And it really writes: on a model with no pin yet, leaving the model
unchanged is NOT an outcome, so a second `uname` cannot draw afresh.
model: refutation on the `m_utsname` field of the written model; no kernel claim. -/
theorem set_utsname_writes_the_pin (bs : List byte) (i : SyscallInput) (m : Model)
    (h0 : m_utsname m = none) : ¬ set_utsname bs i m (Ok () m []) := by
  intro h
  simp only [LinuxProcessSemantics.LinuxProcessSem.Monad.set_utsname,
    LinuxProcessSemantics.LinuxProcessSem.Monad.modify, outcome.Ok.injEq] at h
  obtain ⟨_, hm, _⟩ := h
  have hpin := congrArg m_utsname hm
  rw [m_utsname_with_utsname, h0] at hpin
  exact Option.some_ne_none bs hpin.symm

/-! ## Ticket A16: the /dev/urandom stream setter

This section sits between A11 and A12 rather than at the end of the file
because the end is the anchor another open ticket appends at (BRIEF.md
section 4); in Monad.v `set_urandom` precedes every setter A12 pins.

`set_urandom` has one caller once ported: the delivering branch of Rocq's
`Fs.ReadWrite.read_urandom` (Sys/Fs/ReadWrite.v at a71fd38a), the arm the
`read` and `pread64` dispatches share on `State.FdUrandom`.  That branch
hands the setter `(stream_take_z (m_urandom m) n).2` — the declared stream
past the `n` bytes it has just delivered — after its own gate has checked
that the take was whole; a declaration that runs out is the ARM's decline,
made before the setter is reached.  The pins below are stated on that
argument shape, so what the Lean tree can say today about a read of the
device is said here, and the arm's port inherits it once its own pin fixes
the argument it hands over — the twin of Rocq's
`pread64_urandom_advances_the_stream` (Checks/Cases/Fs/ReadWrite.v).  The
stream laws they lean on are `State.stream_take_z_eq`,
`State.stream_take_rest_self`, `State.stream_take_rest_at` and
`State.ICons_eq_ICons`.

Kernel: Linux v6.18.46, commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5.
Line numbers are drivers/char/random.c unless another file is named.
`urandom_fops` (:1572-1581) reads through `urandom_read_iter` (:1453-1475),
which is `get_random_bytes_user` (:434-482) applied to the request's
iterator (:1474). -/

section TicketA16

variable (i : SyscallInput) (m : Model)

/-- The setter's one admissible outcome: the stream written, no events.
model: `set_urandom s` is `modify (with_urandom s)`, read at its one outcome; no kernel claim. -/
theorem set_urandom_ok (s : InputStream) :
    set_urandom s i m (Ok () (with_urandom s m) []) := rfl

/-- Advancing the stream never leaves the modeled surface.  The declines a
read of the device makes — a declaration shorter than the clamped count,
and a destination only partly writable — are `read_urandom`'s, both taken
before the setter is reached.
model: a `modify` admits no `Unmodeled`; which reads decline is the arm's business, not the setter's. -/
theorem set_urandom_not_unmodeled (s : InputStream) :
    ¬ set_urandom s i m Unmodeled := fun h => nomatch h

/-- THE ADVANCE IS EXACTLY THE DELIVERY.  Handed the remainder of a take of
`n`, the setter leaves the device's stream at the byte as many positions
past the old front as the take delivered, and every later byte in order.
That length is what `get_random_bytes_user` (:434-482) returns: `ret` is
exactly what `copy_to_iter` placed in the user buffer, on the single-copy
path for a count of at most 32 (:455-458) and accumulated block by block
in the loop (:460-476, the sum at :466), and `urandom_read_iter`
(:1453-1475) returns it as the read's result (:1474).  Generator output
that a short copy left undelivered is zeroed (:478, :480), never handed to
a later read.  So the stream the run declares is what the process
receives, and a read consumes exactly the prefix it delivered: no fewer,
or a byte would be delivered twice, and no more, or a declared byte would
reach nobody.
kernel: drivers/char/random.c:get_random_bytes_user,urandom_read_iter@v6.18.46 -/
theorem set_urandom_advances_by_the_delivery (n : Int) (m' : Model) (evs : List event) :
    set_urandom (stream_take_z (m_urandom m) n).2 i m (Ok () m' evs) →
    ∀ k, (m_urandom m').byte_at k
          = (m_urandom m).byte_at ((stream_take_z (m_urandom m) n).1.length + k) := by
  intro h k
  simp only [LinuxProcessSemantics.LinuxProcessSem.Monad.set_urandom,
    LinuxProcessSemantics.LinuxProcessSem.Monad.modify, outcome.Ok.injEq] at h
  obtain ⟨-, rfl, -⟩ := h
  show (stream_take_z (m_urandom m) n).2.byte_at k
        = (m_urandom m).byte_at ((stream_take_z (m_urandom m) n).1.length + k)
  rw [stream_take_z_eq, ← stream_take_rest_self, stream_take_rest_at]

/-- READING `n` BYTES ADVANCES BY `n`: the form the arm reaches, under its
own gate that the take was whole — the declaration held the clamped count.
Then the stream the setter leaves is the old one from position `n` on,
byte for byte.  The gate is the arm's and not the kernel's:
`get_random_bytes_user` (:434-482) stops short of the count only when the
copy into the user buffer comes up short (:456 on the single-copy path,
:467-468 in the loop) or a signal is pending at a page boundary of the
bytes so far (:471-473), and neither is a property of the byte sequence —
so a declaration that ends is an environment that stopped answering, which
the arm declines rather than models as a short read.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem set_urandom_reading_n_advances_by_n (n : Nat) (m' : Model) (evs : List event)
    (hwhole : (stream_take_z (m_urandom m) n).1.length = n) :
    set_urandom (stream_take_z (m_urandom m) n).2 i m (Ok () m' evs) →
    ∀ k, (m_urandom m').byte_at k = (m_urandom m).byte_at (n + k) := by
  intro h k
  rw [set_urandom_advances_by_the_delivery i m n m' evs h k, hwhole]

/-- A ZERO-COUNT READ DRAWS NOTHING.  `get_random_bytes_user` returns 0
before `crng_make_state` is ever called when the iterator is empty
(:440-441), so the generator is not stepped and the next read receives what
this one would have.  Rocq's `read_urandom` answers a zero count without
reaching the setter; this pin is what makes the two spellings agree — handed
a zero take, the setter is the identity on the stream.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem set_urandom_zero_take_leaves_the_stream (m' : Model) (evs : List event) :
    set_urandom (stream_take_z (m_urandom m) 0).2 i m (Ok () m' evs) →
    m_urandom m' = m_urandom m := by
  intro h
  simp only [LinuxProcessSemantics.LinuxProcessSem.Monad.set_urandom,
    LinuxProcessSemantics.LinuxProcessSem.Monad.modify, outcome.Ok.injEq] at h
  obtain ⟨-, rfl, -⟩ := h
  rfl

/-- THE CENSUS SHAPE, first read.  Rocq's `urandom_open_read_close`
(Checks/Cases/Fs/Open.v) drives a sixteen-byte declaration through the
checker as two whole reads of eight and then a decline; this is that shape
at four bytes and reads of two.  The first read delivers the first two
bytes and leaves the other two at the front — so the next read receives
new output of the generator and never the first two again.
`crng_make_state` (:331-387) runs
`crng_fast_key_erasure` (:308-324) on every call, and that overwrites the
key with the first 32 bytes of the block it has just produced (:321), so no
later call can reproduce an earlier call's bytes.
kernel: drivers/char/random.c:crng_make_state,crng_fast_key_erasure@v6.18.46 -/
theorem set_urandom_census_first_read (b1 b2 b3 b4 : byte) (m' : Model) (evs : List event) :
    set_urandom
        (stream_take_z (m_urandom (with_urandom (ICons b1 (ICons b2 (ICons b3 (ICons b4 IEof)))) m))
          2).2
        i (with_urandom (ICons b1 (ICons b2 (ICons b3 (ICons b4 IEof)))) m) (Ok () m' evs) →
    m_urandom m' = ICons b3 (ICons b4 IEof) := by
  intro h
  simp only [LinuxProcessSemantics.LinuxProcessSem.Monad.set_urandom,
    LinuxProcessSemantics.LinuxProcessSem.Monad.modify, outcome.Ok.injEq] at h
  obtain ⟨-, rfl, -⟩ := h
  show (stream_take_z (ICons b1 (ICons b2 (ICons b3 (ICons b4 IEof)))) 2).2
        = ICons b3 (ICons b4 IEof)
  rw [stream_take_z_eq]
  simp only [Int.toNat, stream_take_cons, stream_take_zero]

/-- THE CENSUS SHAPE, second read: from the two bytes the first left, a read
of two leaves the end of the declaration.  The census's next request is
then the arm's decline — the declared stream ran out — not a short read: a
request of at most 32 bytes takes the single-copy path of
`get_random_bytes_user` (:455-458), whose result is the count when the
buffer is wholly writable and, when it faults partway, the prefix
`copy_to_iter` managed or -EFAULT for none (:456, :481) — the partially
writable destination Rocq's arm declines ahead of the setter, so no short
count reaches it.
kernel: drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem set_urandom_census_second_read (b3 b4 : byte) (m' : Model) (evs : List event) :
    set_urandom (stream_take_z (m_urandom (with_urandom (ICons b3 (ICons b4 IEof)) m)) 2).2
        i (with_urandom (ICons b3 (ICons b4 IEof)) m) (Ok () m' evs) →
    m_urandom m' = IEof := by
  intro h
  simp only [LinuxProcessSemantics.LinuxProcessSem.Monad.set_urandom,
    LinuxProcessSemantics.LinuxProcessSem.Monad.modify, outcome.Ok.injEq] at h
  obtain ⟨-, rfl, -⟩ := h
  show (stream_take_z (ICons b3 (ICons b4 IEof)) 2).2 = IEof
  rw [stream_take_z_eq]
  simp only [Int.toNat, stream_take_cons, stream_take_zero]

/-- THE REFUTATIONS.  On any four-byte declaration, a read of two leaves
neither the stream it found — the kernel does not hand the same bytes out
twice, by the key erasure `crng_fast_key_erasure` (:308-324) performs on
every `crng_make_state` (:331-387) — nor a stream advanced by one, which
would deliver the second byte again, nor one advanced by three, which
would consume a byte the process never received.  `ret` in
`get_random_bytes_user` (:456, :466) is the bytes copied out and nothing
else, so the consumed prefix is the delivered one exactly.  On a finite
declaration the three lies differ from the truth in length, so no
distinctness of bytes is assumed; the key erasure is what would be
load-bearing on a periodic infinite declaration, where the model rightly
admits an unchanged stream.
kernel: drivers/char/random.c:get_random_bytes_user,crng_make_state,crng_fast_key_erasure@v6.18.46 -/
theorem set_urandom_consumes_neither_fewer_nor_more (b1 b2 b3 b4 : byte) :
    ∀ s m0, s = ICons b1 (ICons b2 (ICons b3 (ICons b4 IEof))) → m0 = with_urandom s m →
    ¬ set_urandom (stream_take_z (m_urandom m0) 2).2 i m0 (Ok () m0 [])
    ∧ ¬ set_urandom (stream_take_z (m_urandom m0) 2).2 i m0
          (Ok () (with_urandom (ICons b2 (ICons b3 (ICons b4 IEof))) m) [])
    ∧ ¬ set_urandom (stream_take_z (m_urandom m0) 2).2 i m0
          (Ok () (with_urandom (ICons b4 IEof) m) []) := by
  intro s m0 hs hm0
  subst hs hm0
  have hrest : (stream_take_z (ICons b1 (ICons b2 (ICons b3 (ICons b4 IEof)))) 2).2
      = ICons b3 (ICons b4 IEof) := by
    rw [stream_take_z_eq]
    simp only [Int.toNat, stream_take_cons, stream_take_zero]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp only [LinuxProcessSemantics.LinuxProcessSem.Monad.set_urandom,
      LinuxProcessSemantics.LinuxProcessSem.Monad.modify, outcome.Ok.injEq] at h
    obtain ⟨-, hm, -⟩ := h
    have hpin := congrArg m_urandom hm
    change ICons b1 (ICons b2 (ICons b3 (ICons b4 IEof)))
        = (stream_take_z (ICons b1 (ICons b2 (ICons b3 (ICons b4 IEof)))) 2).2 at hpin
    rw [hrest] at hpin
    simp only [ICons_eq_ICons, ICons_ne_IEof, and_false] at hpin
  · simp only [LinuxProcessSemantics.LinuxProcessSem.Monad.set_urandom,
      LinuxProcessSemantics.LinuxProcessSem.Monad.modify, outcome.Ok.injEq] at h
    obtain ⟨-, hm, -⟩ := h
    have hpin := congrArg m_urandom hm
    change ICons b2 (ICons b3 (ICons b4 IEof))
        = (stream_take_z (ICons b1 (ICons b2 (ICons b3 (ICons b4 IEof)))) 2).2 at hpin
    rw [hrest] at hpin
    simp only [ICons_eq_ICons, ICons_ne_IEof, and_false] at hpin
  · simp only [LinuxProcessSemantics.LinuxProcessSem.Monad.set_urandom,
      LinuxProcessSemantics.LinuxProcessSem.Monad.modify, outcome.Ok.injEq] at h
    obtain ⟨-, hm, -⟩ := h
    have hpin := congrArg m_urandom hm
    change ICons b4 IEof
        = (stream_take_z (ICons b1 (ICons b2 (ICons b3 (ICons b4 IEof)))) 2).2 at hpin
    rw [hrest] at hpin
    simp only [ICons_eq_ICons, IEof_ne_ICons, and_false] at hpin

/-- THE DEVICE'S READ MOVES NOTHING BUT ITS STREAM: the descriptor table,
the interpreted file system, standard input and the accept queue are as
they were, and nothing is logged.  `urandom_read_iter` (:1453-1475) reads
nothing off its kiocb, and `urandom_fops`' `.llseek` (:1578) is
`noop_llseek` (fs/read_write.c:324-327), which returns `f_pos` unchanged —
there is no position to move, which is why the stream is the model's and
not the descriptor's, and why a non-negative offset given to `pread64`
changes nothing.  The generator is the one thing `get_random_bytes_user`
(:434-482) draws from, so no other declared stream is consumed.  Rocq's
`pread64_leaves_the_model_alone` (Checks/Cases/Fs/ReadWrite.v) pins the
descriptor table, the file system, standard input and the empty trace of
the arm; the accept queue is added here.
kernel: drivers/char/random.c:urandom_read_iter,get_random_bytes_user;fs/read_write.c:noop_llseek@v6.18.46 -/
theorem set_urandom_moves_only_the_stream (s : InputStream) (m' : Model) (evs : List event) :
    set_urandom s i m (Ok () m' evs) →
    m_fds m' = m_fds m ∧ m_fs m' = m_fs m ∧ m_stdin m' = m_stdin m ∧ m_net m' = m_net m
      ∧ evs = [] := by
  intro h
  simp only [LinuxProcessSemantics.LinuxProcessSem.Monad.set_urandom,
    LinuxProcessSemantics.LinuxProcessSem.Monad.modify, outcome.Ok.injEq] at h
  obtain ⟨-, rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end TicketA16

/-! ## Ticket A12: the signal and terminal setters

Each is a `modify` over the `State` setter, so each has exactly one
outcome and never leaves the surface; the pins that matter are the ones
saying the outcome really moves the model, because a `modify` over a
setter that forgot its field would still close the first two. -/

/-- The setter's one admissible outcome: the halt written, no events.
model: `set_killed` is `modify (with_killed sig)`, read at its one outcome; no kernel claim. -/
theorem set_killed_ok (sig : word) (i : SyscallInput) (m : Model) :
    set_killed sig i m (Ok () (with_killed sig m) []) := rfl

/-- A kill never leaves the modeled surface.
model: a `modify` admits no `Unmodeled`; no kernel claim. -/
theorem set_killed_not_unmodeled (sig : word) (i : SyscallInput) (m : Model) :
    ¬ set_killed sig i m Unmodeled := fun h => nomatch h

/-- A kill really ENDS a running process: leaving the model unchanged is
not an outcome.  The kernel side is `get_signal` (kernel/signal.c)
reaching `do_group_exit` (kernel/exit.c), Linux v6.18.46, commit
1f99e9ab748f, which does not return to the process.
kernel: kernel/signal.c:get_signal; kernel/exit.c:do_group_exit@v6.18.46 -/
theorem set_killed_ends_the_process (sig : word) (i : SyscallInput) (m : Model)
    (h0 : m_halted m = none) : ¬ set_killed sig i m (Ok () m []) := by
  intro h
  simp only [LinuxProcessSemantics.LinuxProcessSem.Monad.set_killed,
    LinuxProcessSemantics.LinuxProcessSem.Monad.modify, outcome.Ok.injEq] at h
  obtain ⟨_, hm, _⟩ := h
  have hh := congrArg m_halted hm
  rw [m_halted_with_killed, h0] at hh
  exact Option.some_ne_none sig hh.symm

/-- The setter's one admissible outcome: the pending bit written, no events.
model: `set_sigabrt_pending` is `modify with_sigabrt_pending`, read at its one outcome; no kernel claim. -/
theorem set_sigabrt_pending_ok (i : SyscallInput) (m : Model) :
    set_sigabrt_pending i m (Ok () (with_sigabrt_pending m) []) := rfl

/-- Recording a pending SIGABRT never leaves the modeled surface.
model: a `modify` admits no `Unmodeled`; no kernel claim. -/
theorem set_sigabrt_pending_not_unmodeled (i : SyscallInput) (m : Model) :
    ¬ set_sigabrt_pending i m Unmodeled := fun h => nomatch h

/-- Sending a BLOCKED SIGABRT does NOT end the process — it stays pending
(`__send_signal_locked` queues it, and the `complete_signal` it calls
wakes nobody for a blocked signal; kernel/signal.c, Linux v6.18.46,
commit 1f99e9ab748f) — so the halt field is untouched and the pending bit
is what moved.
kernel: kernel/signal.c:__send_signal_locked,complete_signal@v6.18.46 -/
theorem set_sigabrt_pending_keeps_running_and_records (i : SyscallInput) (m : Model)
    (m' : Model) (evs : List event) :
    set_sigabrt_pending i m (Ok () m' evs) →
    m_halted m' = m_halted m ∧ m_sigabrt_pending m' = true := by
  intro h
  simp only [LinuxProcessSemantics.LinuxProcessSem.Monad.set_sigabrt_pending,
    LinuxProcessSemantics.LinuxProcessSem.Monad.modify, outcome.Ok.injEq] at h
  obtain ⟨_, rfl, _⟩ := h
  exact ⟨rfl, rfl⟩

/-- The setter's one admissible outcome: the install bit written, no events.
model: `set_sigaltstack_installed` is `modify with_sigaltstack_installed`, read at its one outcome; no kernel claim. -/
theorem set_sigaltstack_installed_ok (i : SyscallInput) (m : Model) :
    set_sigaltstack_installed i m (Ok () (with_sigaltstack_installed m) []) := rfl

/-- Recording the install never leaves the modeled surface.
model: a `modify` admits no `Unmodeled`; no kernel claim. -/
theorem set_sigaltstack_installed_not_unmodeled (i : SyscallInput) (m : Model) :
    ¬ set_sigaltstack_installed i m Unmodeled := fun h => nomatch h

/-- The install branch of `do_sigaltstack` (kernel/signal.c, Linux
v6.18.46, commit 1f99e9ab748f) leaves a NON-ZERO size, and that is the
one thing this setter records: from a fresh process, staying unchanged
is not an outcome.
kernel: kernel/signal.c:do_sigaltstack@v6.18.46 -/
theorem set_sigaltstack_installed_writes (i : SyscallInput) (m : Model)
    (h0 : m_sigaltstack_installed m = false) :
    ¬ set_sigaltstack_installed i m (Ok () m []) := by
  intro h
  simp only [LinuxProcessSemantics.LinuxProcessSem.Monad.set_sigaltstack_installed,
    LinuxProcessSemantics.LinuxProcessSem.Monad.modify, outcome.Ok.injEq] at h
  obtain ⟨_, hm, _⟩ := h
  have hb := congrArg m_sigaltstack_installed hm
  rw [m_sigaltstack_installed_with_sigaltstack_installed, h0] at hb
  exact Bool.noConfusion hb

/-- The setter's one admissible outcome: the pin written, no events.
model: `set_statpin` is `modify (with_statpin p bs)`, read at its one outcome; no kernel claim. -/
theorem set_statpin_ok (p : Fs.path) (bs : List byte) (i : SyscallInput) (m : Model) :
    set_statpin p bs i m (Ok () (with_statpin p bs m) []) := rfl

/-- Pinning a stat never leaves the modeled surface.
model: a `modify` admits no `Unmodeled`; no kernel claim. -/
theorem set_statpin_not_unmodeled (p : Fs.path) (bs : List byte) (i : SyscallInput) (m : Model) :
    ¬ set_statpin p bs i m Unmodeled := fun h => nomatch h

/-- The pin really lands: after the setter the path looks up to the
delivered bytes, so a second `fstat` of the same file answers the same
inode identity rather than drawing afresh.
model: `statpin_lookup` over the written `m_statpins`, by definition; no kernel claim. -/
theorem set_statpin_pins_the_path (p : Fs.path) (bs : List byte) (i : SyscallInput)
    (m m' : Model) (evs : List event) :
    set_statpin p bs i m (Ok () m' evs) →
    statpin_lookup (m_statpins m') p = some bs := by
  intro h
  simp only [LinuxProcessSemantics.LinuxProcessSem.Monad.set_statpin,
    LinuxProcessSemantics.LinuxProcessSem.Monad.modify, outcome.Ok.injEq] at h
  obtain ⟨_, rfl, _⟩ := h
  show statpin_lookup ((p, bs) :: m_statpins m) p = some bs
  rw [statpin_lookup, Fs.path_eqb_refl]
  rfl

/-! ## Ticket D4: the deterministic primitives, read under `bind`

Pins on `Monad.bind_det_iff`, `Monad.bind_det_cases_iff` and their
instances.  What is pinned is that each primitive is read the way
`Monad.bind` defines it — a reader hands the continuation the call's own
value at the model it started in, a setter hands it the written model,
neither adds an event, a decline is the continuation's and never the
primitive's own, and `emit` prepends its events and is NOT of the
event-free shape — and that the inversions
`theories/LinuxProcessSem/Checks/Sys/Prelude.v` proves by hand for a fixed
primitive are each the `→` of an instance: at one outcome for six of
them, and for `bind_input_model_inv` two readings composed at every
outcome.  Those twins carry Rocq's names because they pin the readings'
forward direction in the shape Rocq states it; ticket K1's
`Checks/Sys/Prelude.lean` (PR #766) carries its own hand-proved copies of
the same eight in its own namespace, and reconciling the two — Prelude's
onto the `.1`s here — is a consolidation the second of the two to merge
owes, tracked by R1.  They are marked `model:` and not `rocq-twin:`
because that mark names a lemma in this file's Rocq mirror, and the Rocq
tree has no case file for `Monad`: the lemmas live in
`Checks/Sys/Prelude.v` (`tools/check_lean_pin_evidence.py` says which
file a twin may name).

Each refutation below is stated against a forgery that would be admitted
if the reading were wrong in one specific way — another register for the
number, another input for the call's, a model the setter did not write,
an event a reader or a setter did not emit, a decline neither raised —
and closes by reading the forgery through the instance and deciding the
component that differs. -/

section TicketD4

variable {A : Type} (i : SyscallInput) (m : Model)

/-- Rocq's `input_bind_ok_inv` (Checks/Sys/Prelude.v at f44244ad): the
`Ok` half of `bind_input_iff`'s forward direction.
model: the `→` of `Monad.bind_input_iff` at an `Ok`; twin of `Checks/Sys/Prelude.v`'s `input_bind_ok_inv`. -/
theorem input_bind_ok_inv (k : SyscallInput → Sys A) (x : A) (m' : Model) (evs : List event) :
    bind input k i m (Ok x m' evs) → k i i m (Ok x m' evs) :=
  (bind_input_iff k i m _).1

/-- …and the `Unmodeled` half, Rocq's `input_bind_unmodeled_inv`.
model: the `→` of `Monad.bind_input_iff` at `Unmodeled`; twin of `Checks/Sys/Prelude.v`'s `input_bind_unmodeled_inv`. -/
theorem input_bind_unmodeled_inv (k : SyscallInput → Sys A) :
    bind input k i m Unmodeled → k i i m Unmodeled :=
  (bind_input_iff k i m _).1

/-- Rocq's `get_model_bind_ok_inv`.
model: the `→` of `Monad.bind_get_model_iff` at an `Ok`; twin of `Checks/Sys/Prelude.v`'s `get_model_bind_ok_inv`. -/
theorem get_model_bind_ok_inv (k : Model → Sys A) (x : A) (m' : Model) (evs : List event) :
    bind get_model k i m (Ok x m' evs) → k m i m (Ok x m' evs) :=
  (bind_get_model_iff k i m _).1

/-- Rocq's `get_model_bind_unmodeled_inv`.
model: the `→` of `Monad.bind_get_model_iff` at `Unmodeled`; twin of `Checks/Sys/Prelude.v`'s `get_model_bind_unmodeled_inv`. -/
theorem get_model_bind_unmodeled_inv (k : Model → Sys A) :
    bind get_model k i m Unmodeled → k m i m Unmodeled :=
  (bind_get_model_iff k i m _).1

/-- The `i <- input ;; m <- get_model ;; …` prologue peeled in one step
at every outcome, Rocq's `bind_input_model_inv`, which destructs both
binds by hand at each constructor of `o`; here the two readings composed.
model: `Monad.bind_input_iff` then `Monad.bind_get_model_iff`; twin of `Checks/Sys/Prelude.v`'s `bind_input_model_inv`. -/
theorem bind_input_model_inv (k : SyscallInput → Model → Sys A) (o : outcome A) :
    bind input (fun i0 => bind get_model (fun m0 => k i0 m0)) i m o → k i m i m o :=
  fun h => (bind_get_model_iff _ i m o).1 ((bind_input_iff _ i m o).1 h)

/-- The one-reader peel, Rocq's `bind_model_inv`.
model: the `→` of `Monad.bind_get_model_iff`; twin of `Checks/Sys/Prelude.v`'s `bind_model_inv`. -/
theorem bind_model_inv (k : Model → Sys A) (o : outcome A) :
    bind get_model k i m o → k m i m o :=
  (bind_get_model_iff k i m o).1

/-! ### The readers: the call's own value, the model untouched, no events -/

/-- `input` hands the continuation the call's input.
model: `Monad.bind_input_iff` read at the continuation `pure`; no kernel claim. -/
theorem bind_input_hands_the_call_its_input :
    bind input (fun i0 => Monad.pure i0) i m (Ok i m []) :=
  (bind_input_iff _ i m _).2 (Monad.pure_ok _ i m)

/-- The mistake: some other input.  Refuted on the value.
model: refutation through `Monad.bind_input_iff`; no kernel claim. -/
theorem bind_input_is_not_another_input (i' : SyscallInput) (hne : i' ≠ i) :
    ¬ bind input (fun i0 => Monad.pure i0) i m (Ok i' m []) := by
  intro hb
  have h := (bind_input_iff _ i m _).1 hb
  simp only [Monad.pure, outcome.Ok.injEq] at h
  obtain ⟨h1, -, -⟩ := h
  exact hne h1

/-- A reader never declines on its own: an `Unmodeled` of `input ;; k` has
to be `k`'s, and `pure` never declines.
model: refutation through `Monad.bind_input_iff` at `Unmodeled`; no kernel claim. -/
theorem bind_input_never_declines_alone :
    ¬ bind input (fun i0 => Monad.pure i0) i m Unmodeled :=
  fun hb => nomatch (bind_input_iff _ i m Unmodeled).1 hb

/-- …and the decline side of the same reading, positively: a continuation
that declines is read as the decline it is.
model: `Monad.bind_get_model_iff` at `Unmodeled`; no kernel claim. -/
theorem bind_get_model_passes_a_decline :
    bind get_model (fun _ => (Monad.unmodeled : Sys Unit)) i m Unmodeled :=
  (bind_get_model_iff _ i m Unmodeled).2 rfl

/-- The mistake a reader cannot make: emitting.  A read of the input that
lands with an event is refuted on the event list.
model: refutation through `Monad.bind_input_iff` on the event list; no kernel claim. -/
theorem bind_input_emits_nothing (ev : event) :
    ¬ bind input (fun i0 => Monad.pure i0) i m (Ok i m [ev]) := by
  intro hb
  have h := (bind_input_iff _ i m _).1 hb
  simp only [Monad.pure, outcome.Ok.injEq, reduceCtorEq, and_false] at h

/-- `sysno` is the number the input carries.
model: `Monad.bind_sysno_iff` read at the continuation `pure`; no kernel claim. -/
theorem bind_sysno_reads_the_number :
    bind sysno (fun n => Monad.pure n) i m (Ok i.in_sysno m []) :=
  (bind_sysno_iff _ i m _).2 (Monad.pure_ok _ i m)

/-- The mistake: an argument register read as the number, refuted once the
two are known to differ.
model: refutation through `Monad.bind_sysno_iff`; no kernel claim. -/
theorem bind_sysno_is_not_an_argument (hne : in_arg i 0 ≠ i.in_sysno) :
    ¬ bind sysno (fun n => Monad.pure n) i m (Ok (in_arg i 0) m []) := by
  intro hb
  have h := (bind_sysno_iff _ i m _).1 hb
  simp only [Monad.pure, outcome.Ok.injEq] at h
  obtain ⟨h1, -, -⟩ := h
  exact hne h1

/-- `arg n` is register `n` of the input.
model: `Monad.bind_arg_iff` read at the continuation `pure`; no kernel claim. -/
theorem bind_arg_reads_the_named_register :
    bind (arg 1) (fun a => Monad.pure a) i m (Ok (in_arg i 1) m []) :=
  (bind_arg_iff 1 _ i m _).2 (Monad.pure_ok _ i m)

/-- The mistake: the neighbouring register.
model: refutation through `Monad.bind_arg_iff`; no kernel claim. -/
theorem bind_arg_is_not_another_register (hne : in_arg i 0 ≠ in_arg i 1) :
    ¬ bind (arg 1) (fun a => Monad.pure a) i m (Ok (in_arg i 0) m []) := by
  intro hb
  have h := (bind_arg_iff 1 _ i m _).1 hb
  simp only [Monad.pure, outcome.Ok.injEq] at h
  obtain ⟨h1, -, -⟩ := h
  exact hne h1

/-- `get_model` hands the continuation the model the call started in.
model: `Monad.bind_get_model_iff` read at the continuation `pure`; no kernel claim. -/
theorem bind_get_model_reads_the_model :
    bind get_model (fun m0 => Monad.pure m0) i m (Ok m m []) :=
  (bind_get_model_iff _ i m _).2 (Monad.pure_ok _ i m)

/-- The mistake: some other model.
model: refutation through `Monad.bind_get_model_iff`; no kernel claim. -/
theorem bind_get_model_is_not_another_model (m' : Model) (hne : m' ≠ m) :
    ¬ bind get_model (fun m0 => Monad.pure m0) i m (Ok m' m []) := by
  intro hb
  have h := (bind_get_model_iff _ i m _).1 hb
  simp only [Monad.pure, outcome.Ok.injEq] at h
  obtain ⟨h1, -, -⟩ := h
  exact hne h1

/-- `get_fds` is the table of the model the call started in.
model: `Monad.bind_get_fds_iff` read at the continuation `pure`; no kernel claim. -/
theorem bind_get_fds_reads_the_table :
    bind get_fds (fun fds => Monad.pure fds) i m (Ok (m_fds m) m []) :=
  (bind_get_fds_iff _ i m _).2 (Monad.pure_ok _ i m)

/-- The mistake a reader cannot make: moving the model.  A read of the
table that lands in a model with another ledger is refuted on that ledger.
model: refutation through `Monad.bind_get_fds_iff` on the `m_vmmaps` field; no kernel claim. -/
theorem bind_get_fds_leaves_the_model (h : VmMaps) (hne : m_vmmaps m ≠ h) :
    ¬ bind get_fds (fun _ => Monad.pure ()) i m (Ok () (with_vmmaps h m) []) := by
  intro hb
  have h' := (bind_get_fds_iff _ i m _).1 hb
  simp only [Monad.pure, outcome.Ok.injEq] at h'
  obtain ⟨-, hm, -⟩ := h'
  exact hne ((congrArg m_vmmaps hm).symm.trans (m_vmmaps_with_vmmaps h m))

/-- `get_vmmaps` is the ledger of the model the call started in.
model: `Monad.bind_get_vmmaps_iff` read at the continuation `pure`; no kernel claim. -/
theorem bind_get_vmmaps_reads_the_ledger :
    bind get_vmmaps (fun h => Monad.pure h) i m (Ok (m_vmmaps m) m []) :=
  (bind_get_vmmaps_iff _ i m _).2 (Monad.pure_ok _ i m)

/-- The mistake: another ledger.
model: refutation through `Monad.bind_get_vmmaps_iff`; no kernel claim. -/
theorem bind_get_vmmaps_is_not_another_ledger (h : VmMaps) (hne : h ≠ m_vmmaps m) :
    ¬ bind get_vmmaps (fun h => Monad.pure h) i m (Ok h m []) := by
  intro hb
  have h' := (bind_get_vmmaps_iff _ i m _).1 hb
  simp only [Monad.pure, outcome.Ok.injEq] at h'
  obtain ⟨h1, -, -⟩ := h'
  exact hne h1

/-! ### The setters: the written model, no events

One setter stands for the rest: each instance is `bind_det_iff` at its
`with_*`, and the three pins below read `set_vmmaps` through
`bind_set_vmmaps_iff` exactly as any other would be read through its own. -/

/-- The continuation runs in the written model.
model: `Monad.bind_set_vmmaps_iff` read at the continuation `pure`; no kernel claim. -/
theorem bind_set_vmmaps_writes_the_ledger (h : VmMaps) :
    bind (set_vmmaps h) (fun _ => Monad.pure ()) i m (Ok () (with_vmmaps h m) []) :=
  (bind_set_vmmaps_iff h _ i m _).2 (Monad.pure_ok _ i _)

/-- The mistake: a setter that leaves the model alone.  Refuted on the
field it writes, once the model is known not to hold that value already.
model: refutation through `Monad.bind_set_vmmaps_iff` on the `m_vmmaps` field; no kernel claim. -/
theorem bind_set_vmmaps_really_writes (h : VmMaps) (hne : m_vmmaps m ≠ h) :
    ¬ bind (set_vmmaps h) (fun _ => Monad.pure ()) i m (Ok () m []) := by
  intro hb
  have h' := (bind_set_vmmaps_iff h _ i m _).1 hb
  simp only [Monad.pure, outcome.Ok.injEq] at h'
  obtain ⟨-, hm, -⟩ := h'
  exact hne ((congrArg m_vmmaps hm).trans (m_vmmaps_with_vmmaps h m))

/-- The other mistake: a setter that emits.
model: refutation through `Monad.bind_set_vmmaps_iff` on the event list; no kernel claim. -/
theorem bind_set_vmmaps_emits_nothing (h : VmMaps) (ev : event) :
    ¬ bind (set_vmmaps h) (fun _ => Monad.pure ()) i m (Ok () (with_vmmaps h m) [ev]) := by
  intro hb
  have h' := (bind_set_vmmaps_iff h _ i m _).1 hb
  simp only [Monad.pure, outcome.Ok.injEq, reduceCtorEq, and_false] at h'

/-- A setter never declines on its own either.
model: refutation through `Monad.bind_set_vmmaps_iff` at `Unmodeled`; no kernel claim. -/
theorem bind_set_vmmaps_never_declines_alone (h : VmMaps) :
    ¬ bind (set_vmmaps h) (fun _ => Monad.pure ()) i m Unmodeled :=
  fun hb => nomatch (bind_set_vmmaps_iff h _ i m Unmodeled).1 hb

/-- …and a continuation's decline past a setter is read as a decline, the
written model discarded with it.
model: `Monad.bind_set_vmmaps_iff` at `Unmodeled`; no kernel claim. -/
theorem bind_set_vmmaps_passes_a_decline (h : VmMaps) :
    bind (set_vmmaps h) (fun _ => (Monad.unmodeled : Sys Unit)) i m Unmodeled :=
  (bind_set_vmmaps_iff h _ i m Unmodeled).2 rfl

/-! ### `emit`: events prepended, and not of the event-free shape -/

/-- Two `emit`s in sequence concatenate in program order.
model: `Monad.bind_emit_cases_iff` read at the continuation `emit`; no kernel claim. -/
theorem bind_emit_prepends_its_events (ev ev' : event) :
    bind (emit [ev]) (fun _ => emit [ev']) i m (Ok () m [ev, ev']) :=
  (bind_emit_cases_iff [ev] _ i m _).2 (Or.inl ⟨(), m, [ev'], rfl, rfl⟩)

/-- `emit` is NOT of `bind_det_iff`'s shape: the outcome's events are the
emitted ones followed by the continuation's, never the continuation's
alone, which is why `emit` is read by cases and not as a deterministic
primitive with `[]` for its events.  The forgery here is exactly what the
event-free reading would accept.
model: refutation through `Monad.bind_emit_cases_iff` on the event list; no kernel claim. -/
theorem bind_emit_is_not_event_free (ev : event) :
    ¬ bind (emit [ev]) (fun _ => Monad.pure ()) i m (Ok () m []) := by
  intro hb
  rcases (bind_emit_cases_iff [ev] _ i m _).1 hb with ⟨y, m2, evs2, hk, ho⟩ | ⟨hk, -⟩
  · simp only [Monad.pure, outcome.Ok.injEq] at hk
    obtain ⟨-, rfl, rfl⟩ := hk
    simp only [List.append_nil, outcome.Ok.injEq, reduceCtorEq, and_false] at ho
  · exact absurd hk (by simp only [Monad.pure, reduceCtorEq, not_false_eq_true])

/-- The order is program order and not the reverse: the forgery with the
two events swapped is refuted once they are known to differ.
model: refutation through `Monad.bind_emit_cases_iff` on the event list; no kernel claim. -/
theorem bind_emit_keeps_program_order (ev ev' : event) (hne : ev ≠ ev') :
    ¬ bind (emit [ev]) (fun _ => emit [ev']) i m (Ok () m [ev', ev]) := by
  intro hb
  rcases (bind_emit_cases_iff [ev] _ i m _).1 hb with ⟨y, m2, evs2, hk, ho⟩ | ⟨hk, -⟩
  · simp only [emit, outcome.Ok.injEq] at hk
    obtain ⟨-, rfl, rfl⟩ := hk
    simp only [List.singleton_append, outcome.Ok.injEq, List.cons.injEq, true_and, and_true] at ho
    exact hne ho.2
  · exact absurd hk (by simp only [emit, reduceCtorEq, not_false_eq_true])

/-- …and the decline side of the same reading: an `Unmodeled` past an
`emit` is the continuation's.
model: `Monad.bind_emit_cases_iff` at `Unmodeled`; no kernel claim. -/
theorem bind_emit_passes_a_decline (ev : event) :
    bind (emit [ev]) (fun _ => (Monad.unmodeled : Sys Unit)) i m Unmodeled :=
  (bind_emit_cases_iff [ev] _ i m _).2 (Or.inr ⟨rfl, rfl⟩)

/-- …never `emit`'s own: with a continuation that does not decline, no
`Unmodeled` is admitted.
model: refutation through `Monad.bind_emit_cases_iff` at `Unmodeled`; no kernel claim. -/
theorem bind_emit_never_declines_alone (ev : event) :
    ¬ bind (emit [ev]) (fun _ => Monad.pure ()) i m Unmodeled := by
  intro hb
  rcases (bind_emit_cases_iff [ev] _ i m _).1 hb with ⟨y, m2, evs2, -, ho⟩ | ⟨hk, -⟩
  · cases ho
  · exact absurd hk (by simp only [Monad.pure, reduceCtorEq, not_false_eq_true])

end TicketD4

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Monad
