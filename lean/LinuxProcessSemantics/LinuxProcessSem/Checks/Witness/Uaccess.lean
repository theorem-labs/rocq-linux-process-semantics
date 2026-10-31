import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Witness.Uaccess — the user-buffer boundary witnesses

Mirrors `theories/LinuxProcessSem/Checks/Witness/Uaccess.v`, the witness
side of the boundary `Sys/Uaccess.v` specifies: one definition, the
witness of `Uaccess.access_ok_zero`.  Not part of the trusted
specification.  The spec it witnesses is `Sys.Uaccess.access_ok_zero`
(`Sys/Uaccess.lean`); this file does not import it — the witness needs
only `State.access_okb`, as in Rocq — and the `*_witness_ok` lemma
relating the two arrives with each arm that uses it.  The baseline is the
one `Checks/Sys/Dispatch.lean`'s header explains: the Rocq file is
byte-identical there to `f44244ad6b80`, the commit BRIEF.md names. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Uaccess

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-- `Uaccess.access_ok_zero` as a witness: `k` is the arm's own zero answer
where the range passes `__access_ok` (include/asm-generic/access_ok.h,
Linux v6.18.46: `size <= TASK_SIZE_MAX && addr <= TASK_SIZE_MAX - size`,
transcribed as `State.access_okb`), and -EFAULT where it does not.  That
is the answer of `vfs_read` and `vfs_write` in fs/read_write.c (v6.18.46),
given after the `FMODE_READ`/`FMODE_WRITE` and
`FMODE_CAN_READ`/`FMODE_CAN_WRITE` gates and before `rw_verify_area` in
fs/read_write.c, and of `import_ubuf` in lib/iov_iter.c (v6.18.46) before
a `getrandom`, `sendto` or `recvfrom` transfer — the latter after clamping
`len` to `MAX_RW_COUNT`, where the two `vfs_*` clamp only after the range
test, so that above the clamp this is the `vfs_*` verdict alone and
`import_ubuf`'s only for a count the clamp leaves alone — on a zero-length
transfer exactly as on any other.  In the Rocq tree the `read`/`write` and
socket witnesses consume it; `getrandom`'s witness
(`Checks/Witness/Drivers/Char/Random.v`) tests `access_okb` in place,
because `wait_for_random_bytes` can answer -EINTR before `import_ubuf`
runs and a two-answer witness has no place for that alternative.
Two answers and no third: the argument that the model decides every
range, so that no fail-closed arm belongs here, is on
`Sys.Uaccess.access_ok_zero` (`Sys/Uaccess.lean`) and its Rocq twin. -/
def access_ok_zero_witness (buf count : word) (m : Model) (k : outcome SyscallEffect)
    : outcome SyscallEffect :=
  if access_okb buf (bv_unsigned count) then k
  else ret_outcome (errno_ret EFAULT) m

end LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Uaccess
