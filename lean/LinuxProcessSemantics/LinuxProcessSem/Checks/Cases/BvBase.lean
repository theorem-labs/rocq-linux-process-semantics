import LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! # Checks.Cases.BvBase — kernel pins for the `BvBase` byte encoders

Not part of the trusted specification: QA on the definitions, written to
be READ.  `theories/LinuxProcessSem/Checks/Cases/` has no `BvBase.v`, so
these pins have no Rocq twin; each states what the kernel lays down in
user memory, with the file, function and version it was read from, and
carries a refuting twin.

Ticket A4: `word_le2`, the two bytes `ppoll` stores per `revents`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.BvBase

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-- **A `short` is two little-endian bytes.**  `do_sys_poll` stores each
`revents` with `unsafe_put_user(fds->revents, &ufds->revents, Efault)`
(fs/select.c, `do_sys_poll`, v6.18.46); `revents` is a `short` in
`pollfd` (include/uapi/asm-generic/poll.h, v6.18.46), and riscv is
little-endian (arch/riscv/include/uapi/asm/byteorder.h includes
linux/byteorder/little_endian.h, v6.18.46), so 0x0201 lands as the bytes
01 02.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem pin_word_le2_little_endian : word_le2 0x0201#64 = [1#8, 2#8] := by decide

/-- ...and not big-endian.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem pin_word_le2_not_big_endian : word_le2 0x0201#64 ≠ [2#8, 1#8] := by decide

/-- Two bytes only: a `put_user` of a `short` writes `sizeof(short)`, so bit
16 and above of the word are not stored.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem pin_word_le2_drops_the_high_bytes : word_le2 0x10000#64 = [0#8, 0#8] := by decide

/-- ...and not the four bytes an `int` store (`word_le4`'s width) would leave:
a writeback at that width would overrun `revents` into the next `pollfd`.
kernel: fs/select.c:do_sys_poll@v6.18.46 -/
theorem pin_word_le2_is_not_an_int_store :
    word_le2 0x10005#64 ≠ [0x05#8, 0x00#8, 0x01#8, 0x00#8] := by decide

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.BvBase
