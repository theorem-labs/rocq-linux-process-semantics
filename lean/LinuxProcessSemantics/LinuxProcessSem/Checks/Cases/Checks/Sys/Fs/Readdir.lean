import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Readdir
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Readdir
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Fs.Readdir — what the getdents64 checker answers, read off against Linux

Pins over `Checks.Sys.Fs.Readdir`'s `check_getdents64` and
`getdents64_witness`.  Restates the checker-level half of
`theories/LinuxProcessSem/Checks/Cases/Fs/Readdir.v`: its three `Example`s
are stated on `check_syscall`, one conjunct per answer, and each conjunct
is restated here as one theorem on `check_getdents64` at the same fd and
count, with the same offered effect, on `Checks/Cases/Fs/Readdir.lean`'s
`readdir_model` — Rocq's `getdents64_model` with one fd per further kind
the spec's `match` names appended.  The spec-level half of that file is
`Checks/Cases/Fs/Readdir.lean`'s.  No ledger reads this file's mapping:
`tools/check_lean_cases_parity.py` pairs a Cases file with the Rocq file at
its mirrored path, none sits at this one, so this file is listed
`unmirrored`, and the `Rocq:` name in each twin's docstring is the mapping.
Not part of the trusted specification: this file is QA on the checker,
written to be READ, and every claim in it is a claim about what the kernel
does, with the citation beside it.  Line numbers are fs/readdir.c at Linux
v6.18.46 (commit 1f99e9ab748f) unless another file is named.

WHERE THE DISPATCHER IS PINNED.  The pins above the sentinel apply
`check_getdents64` to the fd and count directly, in
`SYSCALL_DEFINE3(getdents64, fd, dirent, count)`'s order with the
pointer left out, as the spec leaves it out; what they cannot see is a
transposed register in the arm or the `fd32` truncation of a0, and the
`V_Fs_Readdir` section at the end pins those through `check_syscall`
over `checked_table`.  What IS pinned above about truncation is the
count's: the spec reads it through `getdents64_ctx_count`, `struct
dir_context`'s `int`, and the gate pins fix that reading on both sides
of the sign and across 2^32.

WHY A CHECKER NEEDS PINS OF ITS OWN.  The four lemmas of the checker's file
tie `check_getdents64` to `getdents64_spec` in both directions, and a
checker that declined every input, or accepted every return, would still
meet them if the spec were changed to match.  What the lemmas cannot see is
a lie told from OUTSIDE — an errno the kernel would not return, a ledger
beside the one it does, a return that agrees only in its low half — offered
to the checker and required to be refused; nor which of `CheckReject` and
`CheckUnmodeled` the checker answers on an input, which is the difference
between a lie it refuses and a listing it declines, and which no lemma over
`CheckOk` and `CheckUnmodeled` alone fixes.  Rocq puts three examples in
the spec pins' twin, `Checks/Cases/Fs/Readdir.v`, and says why each earns
its place; the sections below keep those reasons short and point at
Rocq's.

HOW THESE CLOSE.  Not by `rfl` alone.  `Model` has no `DecidableEq`, so
`decide` cannot state a pin on the checker, and `rfl` is the closer — but a
bare `rfl` on the directory arm fails the build with `maximum recursion
depth`, for the reason `Checks/Cases/Checks/Sys/Kernel/Time/PosixTimers.lean`'s
header gives and the last section of this file pins: `rfl`'s unifier
reduces under the projection setting `.yesWithDeltaI`, which leaves
`BitVec.toNat` of the closed word stuck, and `getdents64_no_room`'s
`Int.subNatNat` then recurses on the literal 2147483648 instead of folding
(`Checks/Sys/Fs/Readdir.lean`'s header, for what is pinned and what is
not).  `decide` runs `Meta.whnf` under the default setting, which folds
it, so each gate is decided by `decide` as its own pin, rewritten into the
unfolded checker together with the fd-table lookup, and only then is the
rest — constructor matching and `bv_eqb` on closed words — closed by
`rfl`.  Every pin's proof therefore names the gate lemma it rests on, and
nothing in a proof here evaluates the gate except `decide` and the one
`rfl` at the end that pins why.

WHAT MEASURES THESE PINS.  Nothing in the tree: `tools/lean_mutate.py`
builds a spec mutant and elaborates `Checks/Cases/Fs/Readdir.lean` against
it, so no mutant of `Sys/Fs/Readdir.lean` or of the checker is ever
compiled against this file, and its kill-rate is unmeasured by anything
checked in.  This paragraph stops being true when that tool lists a
checker's pins beside the spec's, and is deleted then.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE.  What these pins
prove is that this checker and a named line of Linux agree on what is
accepted, what is refused and what is declined. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Readdir

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Readdir
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Readdir
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Readdir

/-! ## The gate, decided at each count a check names

`getdents64_no_room` is `filldir64`'s `reclen > ctx->count` (fs/readdir.c:367,
Linux v6.18.46) at the smallest `reclen`, 24 (`dirent64_min_reclen`, pinned to
the header in `Checks/Cases/Fs/Readdir.lean`), with `ctx->count` the `int` of
`struct dir_context` that `getdents64` fills from its `unsigned int count`
(fs/readdir.c:398, 403, Linux v6.18.46) — so 2^31 is INT_MIN and has no room,
UINT_MAX is -1, and 2^32 + 24 is 24 again once the prototype has dropped the
high word.
Each is `decide`: `Meta.whnf` under the default setting folds what `rfl`'s
unifier cannot (the header above). -/

/-- 0 bytes: no room.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem no_room_at_0 : getdents64_no_room 0 = true := by decide
/-- 23 bytes: one short of the smallest record, no room.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem no_room_at_23 : getdents64_no_room 23 = true := by decide
/-- 24 bytes: the smallest record fits.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem room_at_24 : getdents64_no_room 24 = false := by decide
/-- INT_MAX as `ctx->count`: room.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem room_at_int_max : getdents64_no_room (Z_to_bv 64 (2 ^ 31 - 1)) = false := by decide
/-- 2^31, INT_MIN as `ctx->count`: `reclen > ctx->count` for every `reclen`.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem no_room_at_2_pow_31 : getdents64_no_room (Z_to_bv 64 (2 ^ 31)) = true := by decide
/-- UINT_MAX, -1 as `ctx->count`: no room.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem no_room_at_uint_max : getdents64_no_room (Z_to_bv 64 (2 ^ 32 - 1)) = true := by decide
/-- 2^32 is 0 after the `unsigned int` prototype drops the high word: no room.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem no_room_at_2_pow_32 : getdents64_no_room (Z_to_bv 64 (2 ^ 32)) = true := by decide
/-- 2^32 + 23 is 23 after the high word is dropped: no room.  With 2^32 (0)
below it and 2^32 + 24 above, the wrapped band's floor is fixed from both
sides, as 23 and 24 fix the unwrapped one.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem no_room_at_2_pow_32_plus_23 :
    getdents64_no_room (Z_to_bv 64 (2 ^ 32 + 23)) = true := by decide
/-- 2^32 + 24 is 24 after the `unsigned int` prototype drops the high word.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem room_at_2_pow_32_plus_24 : getdents64_no_room (Z_to_bv 64 (2 ^ 32 + 24)) = false := by
  decide

/-! ## The fd table, as the checker's `match` reads it

Stated on `m_fds readdir_model`, the discriminant `unfold check_getdents64`
leaves, and not on the projection chain the S file's `sys_simp` lookups use:
`rw` matches syntactically, and these are not registered, so the normal
form the spec pins rely on is untouched.  Which fd holds which kind is
`Checks/Cases/Fs/Readdir.lean`'s to say; each pin below names the kind it
relies on. -/

/-- fd 0, a channel.
model: the fixture's fd table read through `m_fds`, a rewrite for the checker pins. -/
theorem lookup_at_0 : fd_lookup (m_fds readdir_model) 0 = some (.FdChannel 0) := rfl
/-- fd 3, the read-only file.
model: the fixture's fd table read through `m_fds`, a rewrite for the checker pins. -/
theorem lookup_at_3 : fd_lookup (m_fds readdir_model) 3 = some (.FdFile [Z_to_bv 8 102] 7) := rfl
/-- fd 4, the write-only file.
model: the fixture's fd table read through `m_fds`, a rewrite for the checker pins. -/
theorem lookup_at_4 : fd_lookup (m_fds readdir_model) 4 = some (.FdFileW [Z_to_bv 8 103] 9) := rfl
/-- fd 5, the directory.
model: the fixture's fd table read through `m_fds`, a rewrite for the checker pins. -/
theorem lookup_at_5 : fd_lookup (m_fds readdir_model) 5 = some .FdDir := rfl
/-- fd 6, the pipe read end.
model: the fixture's fd table read through `m_fds`, a rewrite for the checker pins. -/
theorem lookup_at_6 : fd_lookup (m_fds readdir_model) 6 = some (.FdPipe 0 false) := rfl
/-- fd 7, the fresh socket.
model: the fixture's fd table read through `m_fds`, a rewrite for the checker pins. -/
theorem lookup_at_7 : fd_lookup (m_fds readdir_model) 7 = some (.FdSocket .SkFresh) := rfl
/-- fd 8, /dev/null.
model: the fixture's fd table read through `m_fds`, a rewrite for the checker pins. -/
theorem lookup_at_8 : fd_lookup (m_fds readdir_model) 8 = some (.FdDevNull true false) := rfl
/-- fd 9, /dev/urandom.
model: the fixture's fd table read through `m_fds`, a rewrite for the checker pins. -/
theorem lookup_at_9 : fd_lookup (m_fds readdir_model) 9 = some .FdUrandom := rfl
/-- fd 99, closed.
model: the fixture's fd table read through `m_fds`, a rewrite for the checker pins. -/
theorem lookup_at_99 : fd_lookup (m_fds readdir_model) 99 = none := rfl

/-! ## Rocq's `getdents64_edge_is_the_minimum_reclen`

A probe learns that the kernel said -EINVAL at some count and listed the
directory at some larger one; it never learns where the MODEL puts the
boundary between them.  `reclen` for "." is `ALIGN(19 + 1 + 1, 8) = 24`
(`filldir64`, fs/readdir.c:355-356, Linux v6.18.46), so `reclen > ctx->count`
(fs/readdir.c:367, Linux v6.18.46) holds at 23 and fails at 24; the third
and fourth pins are what make the first two say what they read as saying. -/

/-- The edge from below: 23 bytes cannot hold a `linux_dirent64`, so
`filldir64` fails the call with -EINVAL, and the checker accepts exactly
that on the unchanged model with no event.  Rocq:
`getdents64_edge_is_the_minimum_reclen`, first conjunct.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem check_count_23_einval_ok :
    check_getdents64 5 23 (mkEffect (errno_ret EINVAL) [] []) readdir_model
      = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_23]
  rfl

/-- …and from above: at 24 the smallest entry fits, the listing is the
kernel's answer, and the checker declines it — for -EINVAL as for any other
return.  Rocq: `getdents64_edge_is_the_minimum_reclen`, second conjunct.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem check_count_24_einval_unmodeled :
    check_getdents64 5 24 (mkEffect (errno_ret EINVAL) [] []) readdir_model
      = CheckUnmodeled := by
  unfold check_getdents64
  rw [lookup_at_5, room_at_24]
  rfl

/-- 23 admits -EINVAL (or the injected -ENOENT) and nothing else: a success
return is a lie, and the checker says so — `CheckReject`, not a decline.
Rocq: `getdents64_edge_is_the_minimum_reclen`, third conjunct.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem check_count_23_success_rejected :
    check_getdents64 5 23 (mkEffect 0 [] []) readdir_model = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_23]
  rfl

/-- 24 declines the very return 23 rejected, so the decline is the COUNT's
doing and not the effect's.  Rocq: `getdents64_edge_is_the_minimum_reclen`,
fourth conjunct.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem check_count_24_listing_unmodeled :
    check_getdents64 5 24 (mkEffect 24 [] []) readdir_model = CheckUnmodeled := by
  unfold check_getdents64
  rw [lookup_at_5, room_at_24]
  rfl

/-- …for EVERY offered effect: with room in the buffer the checker never
reads what it was shown.  The pin the Rocq conjunct above is one instance
of, statable here because the roomy half of the arm is one constructor
whatever `eff` is.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem check_count_24_declines_every_effect (eff : SyscallEffect) :
    check_getdents64 5 24 eff readdir_model = CheckUnmodeled := by
  unfold check_getdents64
  rw [lookup_at_5, room_at_24]
  rfl

/-! ## Rocq's `getdents64_count_is_a_signed_int`

Where the model reads `count` as `struct dir_context`'s `int` rather than
as the `unsigned int` the prototype declares, and no single run separates
the two readings: 2^31 - 1 is the largest positive `ctx->count` and has
room, 2^31 the smallest negative one and has none.  A model comparing the
unsigned low half would have declined both, so the 2^31 pin is the one that
carries the reading, and the 2^32 + 24 pin rules out the other mistake —
that the model simply accepts -EINVAL everywhere above the boundary. -/

/-- INT_MAX as `ctx->count` has room; the listing is declined.  Rocq:
`getdents64_count_is_a_signed_int`, first conjunct.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem check_count_int_max_unmodeled :
    check_getdents64 5 (Z_to_bv 64 (2 ^ 31 - 1)) (mkEffect (errno_ret EINVAL) [] [])
      readdir_model = CheckUnmodeled := by
  unfold check_getdents64
  rw [lookup_at_5, room_at_int_max]
  rfl

/-- 2^31 is INT_MIN as `ctx->count`: `reclen > ctx->count` holds for every
`reclen`, so -EINVAL is accepted — the pin that carries the signed reading,
since an unsigned comparison would have declined it.  Rocq:
`getdents64_count_is_a_signed_int`, second conjunct.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem check_count_2_pow_31_einval_ok :
    check_getdents64 5 (Z_to_bv 64 (2 ^ 31)) (mkEffect (errno_ret EINVAL) [] [])
      readdir_model = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_2_pow_31]
  rfl

/-- UINT_MAX is -1 as `ctx->count`: no room either.  Rocq:
`getdents64_count_is_a_signed_int`, third conjunct.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem check_count_uint_max_einval_ok :
    check_getdents64 5 (Z_to_bv 64 (2 ^ 32 - 1)) (mkEffect (errno_ret EINVAL) [] [])
      readdir_model = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_uint_max]
  rfl

/-- The probe's two `neg` lies: a 0 at 2^31 — a kernel treating INT_MIN as
a large buffer and finding the directory exhausted — and a 24-byte record
at UINT_MAX.  `reclen > ctx->count` holds for every `reclen` when
`ctx->count` is negative (fs/readdir.c:367), so `filldir64` fails the first
emission and no record is delivered: both are refused, not declined.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem check_negative_count_success_and_listing_rejected :
    check_getdents64 5 (Z_to_bv 64 (2 ^ 31)) (mkEffect 0 [] []) readdir_model = CheckReject
    ∧ check_getdents64 5 (Z_to_bv 64 (2 ^ 32 - 1)) (mkEffect 24 [] []) readdir_model
        = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_2_pow_31, no_room_at_uint_max]
  exact ⟨rfl, rfl⟩

/-- 2^32 is 0 after the `unsigned int` prototype drops the high word
(fs/readdir.c:398): no room, and -EINVAL is the answer.  This is the pin
that sees the truncation on the ACCEPTING side: a checker reading the whole
64-bit word finds room here and declines — as it would at 2^31 and
UINT_MAX, which the two pins above already refuse — but a checker that let
the high word count in any other way, declining at 2^32 the way both do at
2^32 + 24, agrees with those two and fails only here and at 2^32 + 23
below.  Rocq's example has no conjunct at this count; its truncation
conjunct is the one at 2^32 + 24, which cannot tell the two checkers
apart.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem check_count_2_pow_32_einval_ok :
    check_getdents64 5 (Z_to_bv 64 (2 ^ 32)) (mkEffect (errno_ret EINVAL) [] [])
      readdir_model = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_2_pow_32]
  rfl

/-- 2^32 + 23 is 23 after the high word is dropped: no room, and -EINVAL is
the answer.  The pin at 2^32 + 24 below fixes the wrapped band's floor from
above only; this one fixes it from below, so a gate that dropped the high
word and then compared the remainder against a floor other than 24 fails
here.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem check_count_2_pow_32_plus_23_einval_ok :
    check_getdents64 5 (Z_to_bv 64 (2 ^ 32 + 23)) (mkEffect (errno_ret EINVAL) [] [])
      readdir_model = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_2_pow_32_plus_23]
  rfl

/-- 2^32 + 24 has room, as 24 does: the high half is discarded first and 24
is left.  A checker reading the whole word would find room here too, so this
pin alone does not see the truncation — `check_count_2_pow_32_einval_ok`
and `check_count_2_pow_32_plus_23_einval_ok` do.  Rocq:
`getdents64_count_is_a_signed_int`, fourth conjunct.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem check_count_2_pow_32_plus_24_unmodeled :
    check_getdents64 5 (Z_to_bv 64 (2 ^ 32 + 24)) (mkEffect (errno_ret EINVAL) [] [])
      readdir_model = CheckUnmodeled := by
  unfold check_getdents64
  rw [lookup_at_5, room_at_2_pow_32_plus_24]
  rfl

/-! ## Rocq's `getdents64_answers_are_inert`

A probe sees only the errno.  That the fds' offsets (7 and 9 here), the file
bodies and the fd table itself came back UNCHANGED, and that no event was
emitted, is a statement about the model's own state, and the equalities
below are the whole of it: the model handed back is the SAME model, and the
event list is empty.  The four kinds after Rocq's six are the fds
`readdir_model` adds for the constructors Rocq's fixture holds none of;
which ops table leaves each without `.iterate_shared` is the spec pins'
evidence in `Checks/Cases/Fs/Readdir.lean`, kind by kind. -/

/-- On the directory fd, -EINVAL for a buffer with no room.  Rocq:
`getdents64_answers_are_inert`, first conjunct.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem check_dir_fd_einval_inert :
    check_getdents64 5 0 (mkEffect (errno_ret EINVAL) [] []) readdir_model
      = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_0]
  rfl

/-- …on the read-only file fd (`iterate_dir`, fs/readdir.c:88-91: no
`.iterate_shared`).  Rocq: `getdents64_answers_are_inert`, second conjunct.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem check_file_fd_enotdir_inert :
    check_getdents64 3 0 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
      = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_3]
  rfl

/-- …on the write-only file fd.  Rocq: `getdents64_answers_are_inert`,
third conjunct.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem check_filew_fd_enotdir_inert :
    check_getdents64 4 0 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
      = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_4]
  rfl

/-- …on a channel (stdin).  Rocq: `getdents64_answers_are_inert`, fourth
conjunct.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem check_channel_fd_enotdir_inert :
    check_getdents64 0 0 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
      = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_0]
  rfl

/-- …on a closed fd (`fd_empty(f)`, fs/readdir.c:409-410).  Rocq:
`getdents64_answers_are_inert`, fifth conjunct.
kernel: fs/readdir.c:getdents64@v6.18.46 -/
theorem check_closed_fd_ebadf_inert :
    check_getdents64 99 0 (mkEffect (errno_ret EBADF) [] []) readdir_model
      = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_99]
  rfl

/-- …and for the injected failure, the removed directory (`iterate_dir`,
fs/readdir.c:105-106), which leaves the model alone too.  Rocq:
`getdents64_answers_are_inert`, sixth conjunct.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem check_dir_fd_enoent_inert :
    check_getdents64 5 0 (mkEffect (errno_ret ENOENT) [] []) readdir_model
      = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_0]
  rfl

/-- …on the pipe read end.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem check_pipe_fd_enotdir_inert :
    check_getdents64 6 0 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
      = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_6]
  rfl

/-- …on the fresh socket.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem check_socket_fd_enotdir_inert :
    check_getdents64 7 0 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
      = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_7]
  rfl

/-- …on /dev/null.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem check_devnull_fd_enotdir_inert :
    check_getdents64 8 0 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
      = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_8]
  rfl

/-- …on /dev/urandom.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem check_urandom_fd_enotdir_inert :
    check_getdents64 9 0 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
      = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_9]
  rfl

/-- The same answers with ROOM in the buffer: the closed fd and every kind
but a directory answer without reading `count` — `getdents64`'s `fd_empty(f)`
test (fs/readdir.c:409-410) and the `.iterate_shared` test of `iterate_dir`
(fs/readdir.c:88-91) both come before the buffer is looked at — so at 4096
the inertness above holds unchanged.  The never-declines pins below say these arms do not DECLINE at
a roomy count; this one says they still ACCEPT, so a kind arm that
rejected everything above the buffer edge fails here and nowhere else.
kernel: fs/readdir.c:getdents64,iterate_dir@v6.18.46 -/
theorem check_other_arms_with_room_still_answer :
    check_getdents64 99 4096 (mkEffect (errno_ret EBADF) [] []) readdir_model
        = CheckOk readdir_model []
    ∧ check_getdents64 0 4096 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
        = CheckOk readdir_model []
    ∧ check_getdents64 3 4096 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
        = CheckOk readdir_model []
    ∧ check_getdents64 4 4096 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
        = CheckOk readdir_model []
    ∧ check_getdents64 6 4096 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
        = CheckOk readdir_model []
    ∧ check_getdents64 7 4096 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
        = CheckOk readdir_model []
    ∧ check_getdents64 8 4096 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
        = CheckOk readdir_model []
    ∧ check_getdents64 9 4096 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
        = CheckOk readdir_model [] := by
  unfold check_getdents64
  rw [lookup_at_99, lookup_at_0, lookup_at_3, lookup_at_4, lookup_at_6, lookup_at_7,
    lookup_at_8, lookup_at_9]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The lies each arm refuses

What the Rocq examples leave to `testing/syscall-check/tests/getdents64_spec.c`,
whose `--mutate` cases pin them against a real kernel: the Lean tree has no
probe replay, so every `reject` case of that probe has its statement on
the checker here, and beside them the lies the probe cannot inject on
every kind — a ledger, or a return agreeing only in its low half, beside
the accepted errno of each arm.  Each is a `CheckReject`, never a decline —
the answer that tells a lie from a listing. -/

/-- A write smuggled beside -EINVAL is rejected on the ledger: `filldir64`
fails the call (fs/readdir.c:366-368) before the `user_write_access_begin`
of include/linux/uaccess.h:568-569, called at fs/readdir.c:374, so no
admitted answer writes a byte.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem check_dir_fd_einval_with_write_rejected :
    check_getdents64 5 0 (mkEffect (errno_ret EINVAL) [(4096, [0])] []) readdir_model
      = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_0]
  rfl

/-- …and so is each of the other four ledgers beside the same -EINVAL: a
zero-fill, an unmap, a copy, a recorded copy-in.  `filldir64` fails the
call (fs/readdir.c:366-368) before the `user_write_access_begin` of
include/linux/uaccess.h:568-569, called at fs/readdir.c:374, and
`getdents64` maps, unmaps and copies nothing on its way there
(fs/readdir.c:397-426), so an admitted answer's five ledgers are all
empty, and the checker tests all five — not the writes alone.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem check_dir_fd_einval_with_other_ledgers_rejected :
    check_getdents64 5 0 (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [(4096, 8)] [] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 5 0 (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(4096, 4096)] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 5 0 (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] []
        [MemCopy.mkCopy 4096 8192 8] []) readdir_model = CheckReject
    ∧ check_getdents64 5 0 (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 1)])
        readdir_model = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_0]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The injected -ENOENT tolerates no ledger either: `iterate_dir` returns
it from the `IS_DEADDIR` test (fs/readdir.c:105-106) before
`.iterate_shared` is called (fs/readdir.c:108), so nothing was written.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem check_dir_fd_enoent_with_write_rejected :
    check_getdents64 5 0 (mkEffect (errno_ret ENOENT) [(4096, [0])] []) readdir_model
      = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_0]
  rfl

/-- …nor any of the other four, for the same reason.  The checker tests the
effect's shape once, before it reads the return, so on the present arm no
mutant can tolerate a zero-fill beside -ENOENT while refusing one beside
-EINVAL; these four are stated so that an arm which came to read the
injected errno through a shape test of its own is caught on every ledger.
kernel: fs/readdir.c:getdents64,iterate_dir@v6.18.46 -/
theorem check_dir_fd_enoent_with_other_ledgers_rejected :
    check_getdents64 5 0 (SyscallEffect.mkEffectU (errno_ret ENOENT) [] [(4096, 8)] [] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 5 0 (SyscallEffect.mkEffectU (errno_ret ENOENT) [] [] [(4096, 4096)] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 5 0 (SyscallEffect.mkEffectU (errno_ret ENOENT) [] [] []
        [MemCopy.mkCopy 4096 8192 8] []) readdir_model = CheckReject
    ∧ check_getdents64 5 0 (SyscallEffect.mkEffectU (errno_ret ENOENT) [] [] [] [] [(4096, 1)])
        readdir_model = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_0]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- -EFAULT is a lie on the small-buffer arm, for the same reason: the
destination is never touched before the -EINVAL.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem check_dir_fd_efault_rejected :
    check_getdents64 5 0 (mkEffect (errno_ret EFAULT) [] []) readdir_model
      = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_0]
  rfl

/-- -EISDIR is `read(2)`'s answer on a directory fd — `generic_read_dir`
(fs/libfs.c:224-227, Linux v6.18.46), the `.read` of
`simple_offset_dir_operations` (fs/libfs.c:568-573) — and nothing on
`getdents64`'s path spells it: a lie on the small-buffer arm, the probe's
`ret=-EISDIR -- small` case.
kernel: fs/readdir.c:iterate_dir,filldir64; fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem check_dir_fd_eisdir_rejected :
    check_getdents64 5 0 (mkEffect (errno_ret EISDIR) [] []) readdir_model
      = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_0]
  rfl

/-- -EACCES and -EPERM are REAL answers this arm refuses: an enforcing LSM
gives the first through `security_file_permission` (security/security.c:2944,
Linux v6.18.46), a `FAN_DENY` listener the second through
`fsnotify_file_perm` (include/linux/fsnotify.h:204, Linux v6.18.46), both
called by `iterate_dir` between its -ENOTDIR and its -ENOENT
(fs/readdir.c:93, 97); the errnos themselves are spelled where a denial
is decided — an enforcing SELinux's `avc_denied` (security/selinux/avc.c:995-1004,
Linux v6.18.46) for -EACCES, `fanotify_get_response` (fs/notify/fanotify/fanotify.c:275,
Linux v6.18.46) for the -EPERM of `FAN_DENY`.  The spec twin refuses both —
bugs/getdents64-lsm-and-fanotify-denials-not-admitted.md records the
narrowing, and `Checks/Cases/Fs/Readdir.lean`'s `dir_fd_no_room_eacces_refused`
and `dir_fd_no_room_eperm_refused` are its falsifiers — so the checker
refuses them, and these two stop closing the day `getdents64_errnos` gains
either.  The probe's `ret=-EACCES` and `ret=-EPERM -- small` cases.
kernel: fs/readdir.c:iterate_dir; security/selinux/avc.c:avc_denied; fs/notify/fanotify/fanotify.c:fanotify_get_response@v6.18.46 -/
theorem check_dir_fd_eacces_eperm_rejected :
    check_getdents64 5 0 (mkEffect (errno_ret EACCES) [] []) readdir_model = CheckReject
    ∧ check_getdents64 5 0 (mkEffect (errno_ret EPERM) [] []) readdir_model = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_0]
  exact ⟨rfl, rfl⟩

/-- A directory has `.iterate_shared`, so `iterate_dir` moves past its first
test (fs/readdir.c:90-91) and -ENOTDIR is a lie on a directory fd.
kernel: fs/readdir.c:iterate_dir,filldir64@v6.18.46 -/
theorem check_dir_fd_enotdir_rejected :
    check_getdents64 5 0 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
      = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_0]
  rfl

/-- …and -EBADF, the answer to an EMPTY fd, is a lie on an open one.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem check_dir_fd_ebadf_rejected :
    check_getdents64 5 0 (mkEffect (errno_ret EBADF) [] []) readdir_model
      = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_0]
  rfl

/-- The -EINVAL of a full buffer is compared at full width: the low 32 bits
of -EINVAL with the high word clear is a different word, and refused.  The
width is decided where `filldir64`'s `int` becomes the syscall's `long` —
`getdents64`'s `return error` (fs/readdir.c:425, Linux v6.18.46) under
`__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:88), which
sign-extends it.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem check_dir_fd_einval_low_half_rejected :
    check_getdents64 5 0 (mkEffect (Z_to_bv 64 (2 ^ 32 - 22)) [] []) readdir_model
      = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_0]
  rfl

/-- `fd_empty(f)` fires before `iterate_dir` is called (fs/readdir.c:409-412),
so on a closed fd -EINVAL — `filldir64`'s answer — is a lie.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem check_closed_fd_einval_rejected :
    check_getdents64 99 0 (mkEffect (errno_ret EINVAL) [] []) readdir_model
      = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_99]
  rfl

/-- …and so is -ENOTDIR, `iterate_dir`'s first answer.
kernel: fs/readdir.c:getdents64,iterate_dir@v6.18.46 -/
theorem check_closed_fd_enotdir_rejected :
    check_getdents64 99 0 (mkEffect (errno_ret ENOTDIR) [] []) readdir_model
      = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_99]
  rfl

/-- The closed fd's -EBADF is compared at full width too: `getdents64`'s
`return -EBADF` (fs/readdir.c:410) is an `int` widened to the syscall's
`long` by `__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:88,
Linux v6.18.46).
kernel: fs/readdir.c:getdents64@v6.18.46 -/
theorem check_closed_fd_ebadf_low_half_rejected :
    check_getdents64 99 0 (mkEffect (Z_to_bv 64 (2 ^ 32 - 9)) [] []) readdir_model
      = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_99]
  rfl

/-- …and a write beside it is refused on the ledger: `getdents64` returns
before the file is looked at.
kernel: fs/readdir.c:getdents64@v6.18.46 -/
theorem check_closed_fd_ebadf_with_write_rejected :
    check_getdents64 99 0 (mkEffect (errno_ret EBADF) [(4096, [0])] []) readdir_model
      = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_99]
  rfl

/-- …and so is each of the other four ledgers beside it — a zero-fill, an
unmap, a copy, a recorded copy-in: `getdents64` returns at `fd_empty(f)`
(fs/readdir.c:409-410) having touched no user memory, so an admitted
-EBADF's five ledgers are all empty and the checker tests all five here as
it does on the directory arm.
kernel: fs/readdir.c:getdents64@v6.18.46 -/
theorem check_closed_fd_ebadf_with_other_ledgers_rejected :
    check_getdents64 99 0 (SyscallEffect.mkEffectU (errno_ret EBADF) [] [(4096, 8)] [] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 99 0 (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [(4096, 4096)] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 99 0 (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] []
        [MemCopy.mkCopy 4096 8192 8] []) readdir_model = CheckReject
    ∧ check_getdents64 99 0 (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] [(4096, 1)])
        readdir_model = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_99]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A closed fd claiming success — the probe's `ret=0 -- badfd` case:
`fd_empty(f)` fires before any file is examined (fs/readdir.c:409-410), so
no fd the table does not hold can have listed anything.
kernel: fs/readdir.c:getdents64@v6.18.46 -/
theorem check_closed_fd_success_rejected :
    check_getdents64 99 0 (mkEffect 0 [] []) readdir_model = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_99]
  rfl

/-- On the read-only file fd, -EBADF is a lie: the fd is open, and it is
`iterate_dir` that answers.
kernel: fs/readdir.c:getdents64,iterate_dir@v6.18.46 -/
theorem check_file_fd_ebadf_rejected :
    check_getdents64 3 0 (mkEffect (errno_ret EBADF) [] []) readdir_model
      = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_3]
  rfl

/-- …and so is -EINVAL: `iterate_dir` returns -ENOTDIR before any actor
runs, at every count.
kernel: fs/readdir.c:iterate_dir,filldir64@v6.18.46 -/
theorem check_file_fd_einval_rejected :
    check_getdents64 3 0 (mkEffect (errno_ret EINVAL) [] []) readdir_model
      = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_3]
  rfl

/-- …and a listing on a file fd with room in the buffer is a lie, not a
decline: the roomy band is the DIRECTORY arm's, and `iterate_dir` never
reaches an actor on a file.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem check_file_fd_listing_rejected :
    check_getdents64 3 4096 (mkEffect 24 [] []) readdir_model = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_3]
  rfl

/-- fd 4, the write-only file: -EBADF is what an O_WRONLY fd gets from
`read` — `vfs_read`'s `!(file->f_mode & FMODE_READ)` (fs/read_write.c:556-557,
Linux v6.18.46) — and not what refuses this call: `fdget_pos` tests no
access mode, and `iterate_dir` (fs/readdir.c:88-91) refuses on the `f_op`
alone.  The probe's `ret=-EBADF -- wfile` case.
kernel: fs/readdir.c:iterate_dir; fs/read_write.c:vfs_read@v6.18.46 -/
theorem check_filew_fd_ebadf_rejected :
    check_getdents64 4 0 (mkEffect (errno_ret EBADF) [] []) readdir_model = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_4]
  rfl

/-- fd 0, the channel: -EINVAL is `filldir64`'s answer and `pipefifo_fops`
has no `.iterate_shared`, so `iterate_dir` (fs/readdir.c:88-91) never
reaches it; -ESPIPE is `lseek`'s answer on the same fd — `vfs_llseek`'s
`FMODE_LSEEK` test (fs/read_write.c:387-388, Linux v6.18.46) — and nothing
on this path spells it.  The probe's `ret=-EINVAL` and `ret=-ESPIPE -- chan`
cases.
kernel: fs/readdir.c:iterate_dir,filldir64; fs/read_write.c:vfs_llseek@v6.18.46 -/
theorem check_channel_fd_einval_espipe_rejected :
    check_getdents64 0 0 (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckReject
    ∧ check_getdents64 0 0 (mkEffect (errno_ret ESPIPE) [] []) readdir_model = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_0]
  exact ⟨rfl, rfl⟩

/-- fd 7, the socket: -ENOTSOCK is what the SOCKET calls answer on an fd
that is not a socket (`sockfd_lookup`, net/socket.c:565-567, Linux v6.18.46);
nothing on `getdents64`'s path calls it, and a socket fd here is -ENOTDIR
like every other non-directory.  The probe's `ret=-ENOTSOCK -- sock` case.
kernel: fs/readdir.c:iterate_dir; net/socket.c:sockfd_lookup@v6.18.46 -/
theorem check_socket_fd_enotsock_rejected :
    check_getdents64 7 0 (mkEffect (errno_ret ENOTSOCK) [] []) readdir_model = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_7]
  rfl

/-- -ENOTDIR is compared at full width on every kind: the low 32 bits of
-ENOTDIR with the high word clear is a different word, and refused on each.
`iterate_dir`'s `int res` (fs/readdir.c:88) is widened to the syscall's
`long` at `getdents64`'s `return error` (fs/readdir.c:425) under
`__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:88, Linux
v6.18.46), so the kernel's word is the sign-extended one.  Width is pinned
for -EBADF and -EINVAL elsewhere in this section; a kind arm comparing
`sint32` of the return would pass every other pin in this file.
kernel: fs/readdir.c:getdents64,iterate_dir@v6.18.46 -/
theorem enotdir_low_half_rejected_on_every_kind :
    check_getdents64 0 0 (mkEffect (Z_to_bv 64 (2 ^ 32 - 20)) [] []) readdir_model
        = CheckReject
    ∧ check_getdents64 3 0 (mkEffect (Z_to_bv 64 (2 ^ 32 - 20)) [] []) readdir_model
        = CheckReject
    ∧ check_getdents64 4 0 (mkEffect (Z_to_bv 64 (2 ^ 32 - 20)) [] []) readdir_model
        = CheckReject
    ∧ check_getdents64 6 0 (mkEffect (Z_to_bv 64 (2 ^ 32 - 20)) [] []) readdir_model
        = CheckReject
    ∧ check_getdents64 7 0 (mkEffect (Z_to_bv 64 (2 ^ 32 - 20)) [] []) readdir_model
        = CheckReject
    ∧ check_getdents64 8 0 (mkEffect (Z_to_bv 64 (2 ^ 32 - 20)) [] []) readdir_model
        = CheckReject
    ∧ check_getdents64 9 0 (mkEffect (Z_to_bv 64 (2 ^ 32 - 20)) [] []) readdir_model
        = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_0, lookup_at_3, lookup_at_4, lookup_at_6, lookup_at_7, lookup_at_8, lookup_at_9]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A ledger beside -ENOTDIR is refused on every kind that is not a
directory, one conjunct per ledger per kind: `iterate_dir` returns -ENOTDIR
at its `.iterate_shared` test (fs/readdir.c:88-91) before any actor runs,
and `getdents64` (fs/readdir.c:397-426) writes, zero-fills, unmaps, copies
and reads nothing on the way there.  The relating lemmas cannot see an
acceptor widened on one arm in both twins at once, and the prelude's own
refutations pin `check_ret_only`, not that an arm uses it; a conjunct here
per arm and per ledger can, which is why each arm carries all five — a
kind arm testing the return alone passes every other pin in this file.
kernel: fs/readdir.c:getdents64,iterate_dir@v6.18.46 -/
theorem enotdir_with_a_ledger_rejected_on_every_kind :
    -- fd 0, the channel: a write, a zero-fill, an unmap, a copy, a copy-in
    check_getdents64 0 0 (mkEffect (errno_ret ENOTDIR) [(4096, [0])] []) readdir_model
        = CheckReject
    ∧ check_getdents64 0 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [(4096, 8)] [] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 0 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] [(4096, 4096)] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 0 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] []
        [MemCopy.mkCopy 4096 8192 8] []) readdir_model = CheckReject
    ∧ check_getdents64 0 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] [] [] [(4096, 1)])
        readdir_model = CheckReject
    -- fd 3, the read-only file: a write, a zero-fill, an unmap, a copy, a copy-in
    ∧ check_getdents64 3 0 (mkEffect (errno_ret ENOTDIR) [(4096, [0])] []) readdir_model
        = CheckReject
    ∧ check_getdents64 3 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [(4096, 8)] [] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 3 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] [(4096, 4096)] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 3 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] []
        [MemCopy.mkCopy 4096 8192 8] []) readdir_model = CheckReject
    ∧ check_getdents64 3 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] [] [] [(4096, 1)])
        readdir_model = CheckReject
    -- fd 4, the write-only file: a write, a zero-fill, an unmap, a copy, a copy-in
    ∧ check_getdents64 4 0 (mkEffect (errno_ret ENOTDIR) [(4096, [0])] []) readdir_model
        = CheckReject
    ∧ check_getdents64 4 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [(4096, 8)] [] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 4 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] [(4096, 4096)] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 4 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] []
        [MemCopy.mkCopy 4096 8192 8] []) readdir_model = CheckReject
    ∧ check_getdents64 4 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] [] [] [(4096, 1)])
        readdir_model = CheckReject
    -- fd 6, the pipe end: a write, a zero-fill, an unmap, a copy, a copy-in
    ∧ check_getdents64 6 0 (mkEffect (errno_ret ENOTDIR) [(4096, [0])] []) readdir_model
        = CheckReject
    ∧ check_getdents64 6 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [(4096, 8)] [] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 6 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] [(4096, 4096)] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 6 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] []
        [MemCopy.mkCopy 4096 8192 8] []) readdir_model = CheckReject
    ∧ check_getdents64 6 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] [] [] [(4096, 1)])
        readdir_model = CheckReject
    -- fd 7, the socket: a write, a zero-fill, an unmap, a copy, a copy-in
    ∧ check_getdents64 7 0 (mkEffect (errno_ret ENOTDIR) [(4096, [0])] []) readdir_model
        = CheckReject
    ∧ check_getdents64 7 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [(4096, 8)] [] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 7 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] [(4096, 4096)] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 7 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] []
        [MemCopy.mkCopy 4096 8192 8] []) readdir_model = CheckReject
    ∧ check_getdents64 7 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] [] [] [(4096, 1)])
        readdir_model = CheckReject
    -- fd 8, /dev/null: a write, a zero-fill, an unmap, a copy, a copy-in
    ∧ check_getdents64 8 0 (mkEffect (errno_ret ENOTDIR) [(4096, [0])] []) readdir_model
        = CheckReject
    ∧ check_getdents64 8 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [(4096, 8)] [] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 8 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] [(4096, 4096)] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 8 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] []
        [MemCopy.mkCopy 4096 8192 8] []) readdir_model = CheckReject
    ∧ check_getdents64 8 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] [] [] [(4096, 1)])
        readdir_model = CheckReject
    -- fd 9, /dev/urandom: a write, a zero-fill, an unmap, a copy, a copy-in
    ∧ check_getdents64 9 0 (mkEffect (errno_ret ENOTDIR) [(4096, [0])] []) readdir_model
        = CheckReject
    ∧ check_getdents64 9 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [(4096, 8)] [] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 9 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] [(4096, 4096)] [] [])
        readdir_model = CheckReject
    ∧ check_getdents64 9 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] []
        [MemCopy.mkCopy 4096 8192 8] []) readdir_model = CheckReject
    ∧ check_getdents64 9 0 (SyscallEffect.mkEffectU (errno_ret ENOTDIR) [] [] [] [] [(4096, 1)])
        readdir_model = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_0, lookup_at_3, lookup_at_4, lookup_at_6, lookup_at_7, lookup_at_8, lookup_at_9]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A success is refused on every kind that is not a directory: fds 0 (the
stdin channel), 4 (the write-only file), 6 (the pipe end), 7 (the socket),
8 (/dev/null) and 9 (/dev/urandom).  `iterate_dir` answers -ENOTDIR when
`.iterate_shared` is NULL before any other test
(fs/readdir.c:88-91), so a 0 from such an fd is a lie whatever `count`.
The inertness pins above offer each kind only its accepted errno, so
without this one a kind arm answering `CheckOk` on every effect would pass
them all.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem check_other_kinds_success_rejected :
    check_getdents64 0 4096 (mkEffect 0 [] []) readdir_model = CheckReject
    ∧ check_getdents64 4 4096 (mkEffect 0 [] []) readdir_model = CheckReject
    ∧ check_getdents64 6 4096 (mkEffect 0 [] []) readdir_model = CheckReject
    ∧ check_getdents64 7 4096 (mkEffect 0 [] []) readdir_model = CheckReject
    ∧ check_getdents64 8 4096 (mkEffect 0 [] []) readdir_model = CheckReject
    ∧ check_getdents64 9 4096 (mkEffect 0 [] []) readdir_model = CheckReject := by
  unfold check_getdents64
  rw [lookup_at_0, lookup_at_4, lookup_at_6, lookup_at_7, lookup_at_8, lookup_at_9]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Nothing declines off the directory arm's roomy half

A checker that answered `CheckUnmodeled` on every input would meet its four
obligations against a spec that declined everywhere, and no lemma of the
checker's file could tell.  `getdents64_spec` declines in one place — a
directory fd with room in the buffer — and these pin that the checker
declines nowhere else: not on a closed fd, not on any kind but a
directory, and not on the directory arm's small-buffer half, whatever the
offered effect. -/

/-- No effect offered on a closed fd is declined.
kernel: fs/readdir.c:getdents64@v6.18.46 -/
theorem closed_fd_never_declines (count : word) (eff : SyscallEffect) :
    check_getdents64 99 count eff readdir_model ≠ CheckUnmodeled := by
  unfold check_getdents64
  rw [lookup_at_99]
  exact check_ret_only_no_unmodeled _ _ _ _

/-- No effect offered on a file fd is declined, at any count.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem file_fd_never_declines (count : word) (eff : SyscallEffect) :
    check_getdents64 3 count eff readdir_model ≠ CheckUnmodeled := by
  unfold check_getdents64
  rw [lookup_at_3]
  exact check_ret_only_no_unmodeled _ _ _ _

/-- Nor is any effect declined on the other kinds, at any count: every
plain-return arm answers without reading `count`, so a kind arm gated on
the buffer would fail here where the inertness pins, at count 0, would not
see it.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem other_kinds_never_decline (count : word) (eff : SyscallEffect) :
    check_getdents64 0 count eff readdir_model ≠ CheckUnmodeled
    ∧ check_getdents64 4 count eff readdir_model ≠ CheckUnmodeled
    ∧ check_getdents64 6 count eff readdir_model ≠ CheckUnmodeled
    ∧ check_getdents64 7 count eff readdir_model ≠ CheckUnmodeled
    ∧ check_getdents64 8 count eff readdir_model ≠ CheckUnmodeled
    ∧ check_getdents64 9 count eff readdir_model ≠ CheckUnmodeled := by
  unfold check_getdents64
  rw [lookup_at_0, lookup_at_4, lookup_at_6, lookup_at_7, lookup_at_8, lookup_at_9]
  exact ⟨check_ret_only_no_unmodeled _ _ _ _, check_ret_only_no_unmodeled _ _ _ _,
    check_ret_only_no_unmodeled _ _ _ _, check_ret_only_no_unmodeled _ _ _ _,
    check_ret_only_no_unmodeled _ _ _ _, check_ret_only_no_unmodeled _ _ _ _⟩

/-- No effect offered on the directory fd with 23 bytes of buffer is
declined.  The proof is the spec pin `count_23_is_enoent_or_einval` through
the checker's `sound_unmodeled` lemma, which is exactly what that lemma is
for: a decline of the checker here would be a decline of the spec, and the
spec admits two answers and no decline at this count.
kernel: fs/readdir.c:iterate_dir,filldir64@v6.18.46 -/
theorem dir_fd_no_room_never_declines (eff : SyscallEffect) :
    check_getdents64 5 23 eff readdir_model ≠ CheckUnmodeled := fun h =>
  ((count_23_is_enoent_or_einval (getdents64_in 5 23) Unmodeled).mp
      (check_getdents64_sound_unmodeled 5 23 eff readdir_model (getdents64_in 5 23) h)).elim
    (fun e => nomatch e) (fun e => nomatch e)

/-- The same refusal on one concrete answer, WITHOUT the checker's lemma in
the proof: the pin above dies with `check_getdents64_sound_unmodeled`, this
one with the checker alone.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem dir_fd_no_room_success_never_declines_directly :
    check_getdents64 5 23 (mkEffect 0 [] []) readdir_model ≠ CheckUnmodeled := by
  intro h
  rw [check_count_23_success_rejected] at h
  cases h

/-! ## The witness

`getdents64_witness` is the checker's accepting answer written out — on the
directory arm -EINVAL, the answer the model derives from `count`, rather
than the injected -ENOENT — and the spec's admission of it
(`getdents64_witness_ok`) is proved beside it.  These pins are the other
half, and open no spec: the answer written out is named against the kernel
line that gives it; it IS the checker's at every fd, count and model; and
it declines exactly where the checker does. -/

/-- At 23 the witness is `filldir64`'s -EINVAL on the unchanged model.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem witness_count_23_is_einval :
    getdents64_witness 5 23 readdir_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) readdir_model [] := by
  unfold getdents64_witness
  rw [lookup_at_5, no_room_at_23]
  rfl

/-- At 24 the witness declines, as the checker does: the listing.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem witness_count_24_is_unmodeled :
    getdents64_witness 5 24 readdir_model = Unmodeled := by
  unfold getdents64_witness
  rw [lookup_at_5, room_at_24]
  rfl

/-- On a closed fd the witness is `fd_empty(f)`'s -EBADF.
kernel: fs/readdir.c:getdents64@v6.18.46 -/
theorem witness_closed_fd_is_ebadf :
    getdents64_witness 99 0 readdir_model
      = Ok (mkEffect (errno_ret EBADF) [] []) readdir_model [] := by
  unfold getdents64_witness
  rw [lookup_at_99]
  rfl

/-- On the read-only file fd the witness is `iterate_dir`'s -ENOTDIR.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem witness_file_fd_is_enotdir :
    getdents64_witness 3 0 readdir_model
      = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  unfold getdents64_witness
  rw [lookup_at_3]
  rfl

/-- …and on every other kind the fixture holds — the channel, the write-only
file, the pipe end, the socket, /dev/null, /dev/urandom — the witness is the
same -ENOTDIR on the unchanged model, read off kind by kind.  The
accepting-witness theorem below says nothing about a witness that DECLINES
a kind; these do.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem witness_other_kinds_are_enotdir :
    getdents64_witness 0 0 readdir_model = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model []
    ∧ getdents64_witness 4 0 readdir_model = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model []
    ∧ getdents64_witness 6 0 readdir_model = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model []
    ∧ getdents64_witness 7 0 readdir_model = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model []
    ∧ getdents64_witness 8 0 readdir_model = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model []
    ∧ getdents64_witness 9 0 readdir_model
        = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  unfold getdents64_witness
  rw [lookup_at_0, lookup_at_4, lookup_at_6, lookup_at_7, lookup_at_8, lookup_at_9]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The checker accepts its own witness at every fd, count and model: the
receptive field and the complete field of the arm meet on the same triple,
which is what makes the arm's `ca_receptive` a statement about
`check_getdents64` and not only about the spec.  The proof opens none of
the checker's four lemmas — it is the lookup split, the gate split,
`ret_outcome_ok_inv` on each answer the witness gives and
`check_ret_only_ok_iff` on every plain arm — so a witness that answered a
kind differently from the checker fails here, on that kind's arm.
model: `getdents64_witness` fed to `check_getdents64`, no spec named -/
theorem check_getdents64_accepts_its_witness (fd count : word) (m : Model)
    (e : SyscallEffect) (m' : Model) (evs : List event)
    (h : getdents64_witness fd count m = Ok e m' evs) :
    check_getdents64 fd count e m = CheckOk m' evs := by
  unfold getdents64_witness at h
  unfold check_getdents64
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    rw [hfd] at h
    dsimp only at h ⊢
    obtain ⟨he, hm, hevs⟩ := ret_outcome_ok_inv _ _ _ _ _ h
    subst he hm hevs
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some k =>
    rw [hfd] at h
    cases k
    case FdFileA _ _ => cases h
    case FdFileRW _ _ => cases h
    case FdDir =>
      cases hroom : getdents64_no_room count with
      | false =>
        simp only [hroom, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
        simp only [hroom, ↓reduceIte] at h ⊢
        obtain ⟨he, hm, hevs⟩ := ret_outcome_ok_inv _ _ _ _ _ h
        subst he hm hevs
        have hne : errno_ret_in getdents64_errnos (errno_ret EINVAL) = false := by decide
        simp only [hne, Bool.false_eq_true, ↓reduceIte, bv_eqb_refl]
    all_goals
      (dsimp only at h ⊢
       obtain ⟨he, hm, hevs⟩ := ret_outcome_ok_inv _ _ _ _ _ h
       subst he hm hevs
       exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)

/-- …and the witness declines at no closed fd and no count: the fail-closed
answer belongs to the directory arm's roomy half alone.
model: `getdents64_witness`'s shape off the directory arm, an `Ok` on every plain arm -/
theorem witness_closed_fd_never_declines (count : word) :
    getdents64_witness 99 count readdir_model ≠ Unmodeled := by
  unfold getdents64_witness
  rw [lookup_at_99]
  exact fun h => nomatch h

/-- …nor on any kind but a directory, at any count.
model: `getdents64_witness`'s shape off the directory arm, an `Ok` on every plain arm -/
theorem witness_other_kinds_never_decline (count : word) :
    getdents64_witness 0 count readdir_model ≠ Unmodeled
    ∧ getdents64_witness 3 count readdir_model ≠ Unmodeled
    ∧ getdents64_witness 4 count readdir_model ≠ Unmodeled
    ∧ getdents64_witness 6 count readdir_model ≠ Unmodeled
    ∧ getdents64_witness 7 count readdir_model ≠ Unmodeled
    ∧ getdents64_witness 8 count readdir_model ≠ Unmodeled
    ∧ getdents64_witness 9 count readdir_model ≠ Unmodeled := by
  unfold getdents64_witness
  rw [lookup_at_0, lookup_at_3, lookup_at_4, lookup_at_6, lookup_at_7, lookup_at_8, lookup_at_9]
  exact ⟨(fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h),
    (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h)⟩

/-- The converse of `check_getdents64_accepts_its_witness`, at every fd,
count and model: where the witness declines, the checker declines.  The
accepting-witness theorem is vacuous on a witness that answers `Unmodeled`
where the checker answers, so a witness declining a kind — or the
small-buffer half of the directory arm — would pass it, and only
`getdents64_witness_ok` in the checker's file would notice; this pin
notices on the checker, by the same lookup and gate split, opening none of
the checker's lemmas.
model: `getdents64_witness`'s declines read against `check_getdents64`'s, no spec named -/
theorem witness_declines_only_where_the_checker_declines (fd count : word) (m : Model)
    (eff : SyscallEffect) (h : getdents64_witness fd count m = Unmodeled) :
    check_getdents64 fd count eff m = CheckUnmodeled := by
  unfold getdents64_witness at h
  unfold check_getdents64
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    rw [hfd] at h
    exact nomatch h
  | some k =>
    rw [hfd] at h
    cases k
    case FdFileA _ _ => rfl
    case FdFileRW _ _ => rfl
    case FdDir =>
      cases hroom : getdents64_no_room count with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]
      | true =>
        simp only [hroom, ↓reduceIte] at h
        exact nomatch h
    all_goals exact nomatch h

/-! ## The header's claim about the elaborator, pinned

`getdents64_no_room 23 = true` is what every closed pin above proves by
`decide` and rewrites in because `rfl` cannot: under the option that turns
the projection setting off, `rfl` can.  When this stops elaborating, either
the option or the mechanism has changed, and the checker's header and
`Checks/Cases/Checks/Sys/Kernel/Time/PosixTimers.lean` are what to reread. -/

set_option backward.isDefEq.lazyWhnfCore false in
/-- `no_room_at_23` by plain `rfl`, under the option that turns the
projection setting off: the same `reclen > ctx->count` at 23.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
example : getdents64_no_room 23 = true := rfl

-- lean-port sentinel: ticket V-Fs-Readdir appends below this line

section V_Fs_Readdir

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Fs-Readdir — getdents64 over the real table

WHAT IS STATED HERE.  Rocq's three dispatcher examples, the recorded
calls in getdents64_spec and the related directory probes, and register
readings that separate this arm from a transposed or untruncated one.

WHAT A PIN HERE ADDS.  The checker-level pins above bypass table lookup
and argument extraction.  `lookup_dents_in` fixes the row;
`count_is_a2_over_the_real_table` and
`fd_is_the_low_half_of_a0_over_the_real_table` fix those readings.

POLARITY.  Kernel evidence accompanies accepted answers, rejected lies,
and the checker's declines; the lookup and dispatcher reduction are model
facts.  The three Rocq twins name their source examples and file beside
the kernel evidence.
Kernel locations below are Linux v6.18.46, commit 1f99e9ab748f. -/

/-- The three argument registers, with integer values reduced modulo 2^64. -/
def dents_in (fd buf count : Int) : SyscallInput :=
  SyscallInput.mkInput 61 [Z_to_bv 64 fd, Z_to_bv 64 buf, Z_to_bv 64 count, 0, 0, 0]
    (fun _ => none) (fun _ => none)

/-- The dispatcher lookup at the fixture's syscall number.
model: `lookup_ca` over `checked_table` at 61. -/
theorem lookup_dents_in (fd buf count : Int) :
    lookup_ca checked_table (bv_unsigned (dents_in fd buf count).in_sysno) =
      some arm_getdents64 := rfl

/-- Expose the arm without reducing the directory gate.
model: the registered arm's dispatcher reduction. -/
theorem check_syscall_dents_in (fd buf count : Int) (eff : SyscallEffect) (m : Model) :
    check_syscall (dents_in fd buf count) eff m =
      check_getdents64 (fd32 (Z_to_bv 64 fd)) (Z_to_bv 64 count) eff m := rfl

/-- The count gate on the register fixture's word construction.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem no_room_z0 : getdents64_no_room (Z_to_bv 64 0) = true := by decide

/-- The count gate on the register fixture's word construction.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem no_room_z23 : getdents64_no_room (Z_to_bv 64 23) = true := by decide

/-- The count gate on the register fixture's word construction.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem room_z24 : getdents64_no_room (Z_to_bv 64 24) = false := by decide

/-- The three-argument arm with arbitrary later registers.
model: the registered arm's dispatcher reduction on six words. -/
theorem check_syscall_dents_regs (fd buf count a3 a4 a5 : word)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (SyscallInput.mkInput 61 [fd, buf, count, a3, a4, a5]
      (fun _ => none) (fun _ => none)) eff m =
      check_getdents64 (fd32 fd) count eff m := rfl

/-- Witness argument routing follows getdents64's prototype
(fs/readdir.c:397-398), SC_RISCV_REGS_TO_ARGS
(arch/riscv/include/asm/syscall_wrapper.h:21-24), and __SC_CAST
(include/linux/syscalls.h:132), Linux v6.18.46, commit 1f99e9ab748f.
kernel: fs/readdir.c:getdents64; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem witness_dents_in (fd buf count : Int) (m : Model) :
    syscall_spec_witness (dents_in fd buf count) m =
      getdents64_witness (fd32 (Z_to_bv 64 fd)) (Z_to_bv 64 count) m := rfl

/-- A probe does not reveal the model's exact buffer-size edge; Rocq's
`getdents64_in` parks the buffer at 4096, which is `dents_in _ 4096 _` here.
Rocq: `Checks.Cases.Fs.Readdir.getdents64_edge_is_the_minimum_reclen`
(theories/LinuxProcessSem/Checks/Cases/Fs/Readdir.v)
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem getdents64_edge_is_the_minimum_reclen :
    check_syscall (dents_in 5 4096 23) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 5 4096 24) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckUnmodeled
    ∧ check_syscall (dents_in 5 4096 23) (mkEffect 0 [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 5 4096 24) (mkEffect 24 [] []) readdir_model = CheckUnmodeled := by
  simp only [check_syscall_dents_in]
  exact ⟨by
      change check_getdents64 5 (Z_to_bv 64 23) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z23]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 24) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, room_z24]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 23) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z23]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 24) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, room_z24]
      rfl⟩

/-- No single run separates the signed `int` reading of count from the
prototype's unsigned reading.
Rocq: `Checks.Cases.Fs.Readdir.getdents64_count_is_a_signed_int`
(theories/LinuxProcessSem/Checks/Cases/Fs/Readdir.v)
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem getdents64_count_is_a_signed_int :
    check_syscall (dents_in 5 4096 (2 ^ 31 - 1)) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckUnmodeled
    ∧ check_syscall (dents_in 5 4096 (2 ^ 31)) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 5 4096 (2 ^ 32 - 1)) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 5 4096 (2 ^ 32 + 24)) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckUnmodeled := by
  simp only [check_syscall_dents_in]
  exact ⟨by
      change check_getdents64 5 (Z_to_bv 64 (2 ^ 31 - 1)) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, room_at_int_max]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 (2 ^ 31)) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_at_2_pow_31]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 (2 ^ 32 - 1)) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_at_uint_max]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 (2 ^ 32 + 24)) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, room_at_2_pow_32_plus_24]
      rfl⟩

/-- Offsets, file bodies, the fd table, and events are model state that
no observation of a probe's errno reveals.
Rocq: `Checks.Cases.Fs.Readdir.getdents64_answers_are_inert`
(theories/LinuxProcessSem/Checks/Cases/Fs/Readdir.v)
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64@v6.18.46 -/
theorem getdents64_answers_are_inert :
    check_syscall (dents_in 5 4096 0) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 3 4096 0) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 4 4096 0) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 0 4096 0) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 99 4096 0) (mkEffect (errno_ret EBADF) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 5 4096 0) (mkEffect (errno_ret ENOENT) [] []) readdir_model = CheckOk readdir_model [] := by
  simp only [check_syscall_dents_in]
  exact ⟨by
      change check_getdents64 5 (Z_to_bv 64 0) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z0]
      rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 0) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z0]
      rfl⟩

/-- Trace 030: the channel answers follow iterate_dir (fs/readdir.c:88-91,
Linux v6.18.46, commit 1f99e9ab748f).
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64@v6.18.46 -/
theorem chan_enotdir_accepted_over_the_real_table :
    check_syscall (dents_in 0 73744 4096) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 1 73744 4096) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 2 73744 4096) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckOk readdir_model [] := by
  simp only [check_syscall_dents_in]
  exact ⟨rfl,
    rfl,
    rfl⟩

/-- Traces 031-032 replace that iterate_dir answer with EINVAL or ESPIPE
(fs/readdir.c:88-91, Linux v6.18.46, commit 1f99e9ab748f).
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64; include/uapi/asm-generic/errno-base.h:ESPIPE@v6.18.46 -/
theorem chan_lies_rejected_over_the_real_table :
    check_syscall (dents_in 0 73744 4096) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 0 73744 4096) (mkEffect (errno_ret ESPIPE) [] []) readdir_model = CheckReject := by
  simp only [check_syscall_dents_in]
  exact ⟨rfl,
    rfl⟩

/-- The small-buffer calls reach filldir64's EINVAL (fs/readdir.c:349-368);
trace 010 injects iterate_dir's ENOENT (:105-106), Linux v6.18.46, commit 1f99e9ab748f.
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64@v6.18.46 -/
theorem small_accepted_over_the_real_table :
    check_syscall (dents_in 5 73744 0) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 5 73744 1) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 5 73744 23) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 5 73744 0) (mkEffect (errno_ret ENOENT) [] []) readdir_model = CheckOk readdir_model [] := by
  have hroom1 : getdents64_no_room (Z_to_bv 64 1) = true := by decide
  simp only [check_syscall_dents_in]
  exact ⟨by
      change check_getdents64 5 (Z_to_bv 64 0) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z0]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 1) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, hroom1]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 23) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z23]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 0) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z0]
      rfl⟩

/-- The small-buffer return and smuggle-write lies are refused around
filldir64 (fs/readdir.c:349-368, Linux v6.18.46, commit 1f99e9ab748f).
The EACCES/EPERM refusals inherit the declared narrowing in
bugs/getdents64-lsm-and-fanotify-denials-not-admitted.md.
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64; include/uapi/asm-generic/errno-base.h:EISDIR,EACCES,EPERM@v6.18.46 -/
theorem small_lies_rejected_over_the_real_table :
    check_syscall (dents_in 5 73744 0) (mkEffect 0 [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 5 73744 0) (mkEffect (errno_ret EFAULT) [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 5 73744 0) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 5 73744 0) (mkEffect (errno_ret EBADF) [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 5 73744 0) (mkEffect (errno_ret EISDIR) [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 5 73744 0) (mkEffect (errno_ret EACCES) [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 5 73744 0) (mkEffect (errno_ret EPERM) [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 5 73744 23) (mkEffect 24 [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 5 73744 0) (mkEffect (errno_ret EINVAL) [(73744, [0, 0, 0, 0, 0, 0, 0, 0])] []) readdir_model = CheckReject := by
  simp only [check_syscall_dents_in]
  exact ⟨by
      change check_getdents64 5 (Z_to_bv 64 0) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z0]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 0) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z0]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 0) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z0]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 0) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z0]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 0) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z0]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 0) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z0]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 0) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z0]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 23) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z23]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 0) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z0]
      rfl⟩

/-- Trace 013: the signed ctx.count makes filldir64's comparison fail
(fs/readdir.c:367-368, Linux v6.18.46, commit 1f99e9ab748f).
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64@v6.18.46 -/
theorem neg_count_accepted_over_the_real_table :
    check_syscall (dents_in 5 73744 (2 ^ 31)) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 5 73744 (2 ^ 32 - 1)) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckOk readdir_model [] := by
  simp only [check_syscall_dents_in]
  exact ⟨by
      change check_getdents64 5 (Z_to_bv 64 (2 ^ 31)) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_at_2_pow_31]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 (2 ^ 32 - 1)) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_at_uint_max]
      rfl⟩

/-- Traces 014-015 offer success at negative ctx.count to filldir64's
small-buffer branch (fs/readdir.c:367-368, Linux v6.18.46, commit 1f99e9ab748f).
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64@v6.18.46 -/
theorem neg_count_lies_rejected_over_the_real_table :
    check_syscall (dents_in 5 73744 (2 ^ 31)) (mkEffect 0 [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 5 73744 (2 ^ 32 - 1)) (mkEffect 24 [] []) readdir_model = CheckReject := by
  simp only [check_syscall_dents_in]
  exact ⟨by
      change check_getdents64 5 (Z_to_bv 64 (2 ^ 31)) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_at_2_pow_31]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 (2 ^ 32 - 1)) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_at_uint_max]
      rfl⟩

/-- The recorded roomy calls (019-023, dirfd_spec 054, and
scenarios/dir_name_unlink 012-013) need the listing beyond filldir64's
size gate (fs/readdir.c:367-368, Linux v6.18.46, commit 1f99e9ab748f).
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64@v6.18.46 -/
theorem above_band_declined_over_the_real_table :
    check_syscall (dents_in 5 73744 4096) (mkEffect 48 [] []) readdir_model = CheckUnmodeled
    ∧ check_syscall (dents_in 5 73744 4096) (mkEffect 224 [] []) readdir_model = CheckUnmodeled
    ∧ check_syscall (dents_in 5 73744 4096) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckUnmodeled
    ∧ check_syscall (dents_in 5 73744 (2 ^ 32 + 24)) (mkEffect 24 [] []) readdir_model = CheckUnmodeled
    ∧ check_syscall (dents_in 5 73744 (2 ^ 31 - 1)) (mkEffect 48 [] []) readdir_model = CheckUnmodeled := by
  have hroom4096 : getdents64_no_room (Z_to_bv 64 4096) = false := by decide
  simp only [check_syscall_dents_in]
  exact ⟨by
      change check_getdents64 5 (Z_to_bv 64 4096) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, hroom4096]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 4096) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, hroom4096]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 4096) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, hroom4096]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 (2 ^ 32 + 24)) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, room_at_2_pow_32_plus_24]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 (2 ^ 31 - 1)) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, room_at_int_max]
      rfl⟩

/-- File, pipe and socket calls (024, 028, 033, 035), plus openat_rdwr 048
and scenarios/file_size_offset 001, use iterate_dir's ENOTDIR
(fs/readdir.c:88-91, Linux v6.18.46, commit 1f99e9ab748f).
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64@v6.18.46 -/
theorem nondir_answers_over_the_real_table :
    check_syscall (dents_in 3 73744 4096) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 4 73744 4096) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 6 73744 4096) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 7 73744 4096) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 3 73744 64) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckOk readdir_model [] := by
  simp only [check_syscall_dents_in]
  exact ⟨rfl,
    rfl,
    rfl,
    rfl,
    rfl⟩

/-- The corresponding return lies (025-027, 029, 034, 036-037 and
openat_rdwr 052) contradict iterate_dir's ENOTDIR branch
(fs/readdir.c:88-91, Linux v6.18.46, commit 1f99e9ab748f).
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64; include/uapi/asm-generic/errno.h:ENOTSOCK@v6.18.46 -/
theorem nondir_lies_rejected_over_the_real_table :
    check_syscall (dents_in 3 73744 4096) (mkEffect 0 [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 3 73744 4096) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 3 73744 4096) (mkEffect (errno_ret EBADF) [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 4 73744 4096) (mkEffect (errno_ret EBADF) [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 6 73744 4096) (mkEffect 0 [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 7 73744 4096) (mkEffect (errno_ret ENOTSOCK) [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 7 73744 4096) (mkEffect 0 [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 3 73744 64) (mkEffect 0 [] []) readdir_model = CheckReject := by
  simp only [check_syscall_dents_in]
  exact ⟨rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl⟩

/-- Closed descriptors, including trace 038: fd_empty(f) returns EBADF
before iterate_dir reads count (getdents64, fs/readdir.c:409-412,
Linux v6.18.46, commit 1f99e9ab748f).
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64@v6.18.46 -/
theorem badfd_over_the_real_table :
    check_syscall (dents_in 99 73744 4096) (mkEffect (errno_ret EBADF) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 99 73744 0) (mkEffect (errno_ret EBADF) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 9999 73744 4096) (mkEffect (errno_ret EBADF) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in (2 ^ 64 - 1) 73744 4096) (mkEffect (errno_ret EBADF) [] []) readdir_model = CheckOk readdir_model [] := by
  simp only [check_syscall_dents_in]
  exact ⟨rfl,
    rfl,
    rfl,
    rfl⟩

/-- Traces 039-041: fd_empty(f) decides EBADF before iterate_dir reads
count (getdents64, fs/readdir.c:409-412, Linux v6.18.46, commit 1f99e9ab748f).
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64@v6.18.46 -/
theorem badfd_lies_rejected_over_the_real_table :
    check_syscall (dents_in 99 73744 4096) (mkEffect 0 [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 99 73744 4096) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in 99 73744 0) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckReject := by
  simp only [check_syscall_dents_in]
  exact ⟨rfl,
    rfl,
    rfl⟩

/-- Transposing a1/a2 swaps the two gates: SC_RISCV_REGS_TO_ARGS
(arch/riscv/include/asm/syscall_wrapper.h:21-24) follows the getdents64
prototype (fs/readdir.c:397-398), Linux v6.18.46, commit 1f99e9ab748f.
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem count_is_a2_over_the_real_table :
    check_syscall (dents_in 5 4096 23) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in 5 23 4096) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckUnmodeled := by
  have hroom4096 : getdents64_no_room (Z_to_bv 64 4096) = false := by decide
  simp only [check_syscall_dents_in]
  exact ⟨by
      change check_getdents64 5 (Z_to_bv 64 23) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z23]
      rfl,
    by
      change check_getdents64 5 (Z_to_bv 64 4096) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, hroom4096]
      rfl⟩

/-- The trunc calls (042-044) exercise __SC_CAST to unsigned int
(include/linux/syscalls.h:132; getdents64, fs/readdir.c:397-398;
SC_RISCV_REGS_TO_ARGS, arch/riscv/include/asm/syscall_wrapper.h:21-24),
Linux v6.18.46, commit 1f99e9ab748f.  Reading a0 at full width loses the
directory, file, and pipe aliases.
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem fd_is_the_low_half_of_a0_over_the_real_table :
    check_syscall (dents_in (2 ^ 32 + 5) 73744 23) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in (2 ^ 32 + 3) 73744 4096) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in (2 ^ 32 + 3) 73744 4096) (mkEffect (errno_ret EBADF) [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in (2 ^ 32 + 12345) 73744 4096) (mkEffect (errno_ret EBADF) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (dents_in (2 ^ 32 + 12345) 73744 4096) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckReject
    ∧ check_syscall (dents_in (4 * 2 ^ 32 + 6) 73744 4096) (mkEffect (errno_ret ENOTDIR) [] []) readdir_model = CheckOk readdir_model [] := by
  simp only [check_syscall_dents_in]
  exact ⟨by
      change check_getdents64 5 (Z_to_bv 64 23) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_z23]
      rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl⟩

/-- Later registers separate the three-argument prototype from extra inputs:
getdents64 (fs/readdir.c:397-398) and SC_RISCV_REGS_TO_ARGS
(arch/riscv/include/asm/syscall_wrapper.h:21-24), Linux v6.18.46,
commit 1f99e9ab748f.
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem registers_after_a2_unread_over_the_real_table :
    check_syscall (SyscallInput.mkInput 61
      [5, 4096, 23, 1, Z_to_bv 64 (2 ^ 63), Z_to_bv 64 (2 ^ 64 - 1)]
      (fun _ => none) (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckOk readdir_model []
    ∧ check_syscall (SyscallInput.mkInput 61
      [5, 4096, 4096, 1, Z_to_bv 64 (2 ^ 63), Z_to_bv 64 (2 ^ 64 - 1)]
      (fun _ => none) (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckUnmodeled := by
  have hroom : getdents64_no_room 4096 = false := by decide
  have hfd : fd32 5 = 5 := by decide
  simp only [check_syscall_dents_regs, hfd]
  unfold check_getdents64
  rw [lookup_at_5, no_room_at_23, hroom]
  exact ⟨rfl, rfl⟩

/-- The unsigned int parameter followed by int ctx.count sees 23 again
(getdents64, fs/readdir.c:397-403; __SC_CAST, include/linux/syscalls.h:132;
struct dir_context, include/linux/fs.h:2210), Linux v6.18.46, commit 1f99e9ab748f.
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem count_high_half_discarded_over_the_real_table :
    check_syscall (dents_in 5 73744 (2 ^ 32 + 23)) (mkEffect (errno_ret EINVAL) [] []) readdir_model = CheckOk readdir_model [] := by
  simp only [check_syscall_dents_in]
  exact by
      change check_getdents64 5 (Z_to_bv 64 (2 ^ 32 + 23)) _ _ = _
      unfold check_getdents64
      rw [lookup_at_5, no_room_at_2_pow_32_plus_23]
      rfl

/-- The witness selects filldir64's EINVAL, or iterate_dir's ENOTDIR,
and declines a listing (fs/readdir.c:349-368, :88-91, getdents64 at
:397-426, Linux v6.18.46, commit 1f99e9ab748f).
kernel: fs/readdir.c:getdents64,filldir64,iterate_dir@v6.18.46 -/
theorem witness_over_the_real_table :
    syscall_spec_witness (dents_in 5 4096 23) readdir_model =
      Ok (mkEffect (errno_ret EINVAL) [] []) readdir_model []
    ∧ syscall_spec_witness (dents_in 5 4096 4096) readdir_model = Unmodeled
    ∧ syscall_spec_witness (dents_in 3 4096 4096) readdir_model =
      Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model []
    ∧ syscall_spec_witness (dents_in (2 ^ 32 + 5) 4096 23) readdir_model =
      Ok (mkEffect (errno_ret EINVAL) [] []) readdir_model [] := by
  have hfd5 : fd32 (Z_to_bv 64 5) = 5 := by decide
  have hfd3 : fd32 (Z_to_bv 64 3) = 3 := by decide
  have hfdhi : fd32 (Z_to_bv 64 (2 ^ 32 + 5)) = 5 := by decide
  have hroomz : getdents64_no_room (Z_to_bv 64 4096) = false := by decide
  simp only [witness_dents_in, hfd5, hfd3, hfdhi]
  unfold getdents64_witness
  rw [lookup_at_5, lookup_at_3, no_room_z23, hroomz]
  exact ⟨rfl, rfl, rfl, rfl⟩

end V_Fs_Readdir

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Readdir
