// Target translation of arena-tee: drain stdin into an anonymous mmap'd
// page (at most CAP = 4088 bytes, stored at arena offset 8 onward), then
// write to fd 2 exactly 8 + n bytes: the byte count n as eight lowercase
// hex digits zero-padded to 32 bits, immediately followed by the n drained
// bytes.  Arguments are ignored; nothing goes to stdout.
//
// mmap failure -> exit 1 (no output); read error -> exit 2; write error ->
// exit 3; otherwise exit 0.
//
// Simplifications relative to the C source, none of them observable: the
// eight header digits are emitted by one byte-at-a-time constant-trip loop
// over the arena's first 8 bytes rather than by two packed 4-byte stores,
// and there are no helper functions for the hex packing.
const linux = @import("std").os.linux;

const PROT_RW: usize = 3; // PROT_READ | PROT_WRITE
const MAP_PRIVATE_ANON: usize = 0x22; // MAP_PRIVATE | MAP_ANONYMOUS
const NO_FD: usize = @bitCast(@as(isize, -1));

const HDR: usize = 8; // eight hex digits, no separator
const CAP: usize = 4088; // 4096 - HDR: the arena is exactly one page

// write all n bytes to fd 2; -1 on write error, like the source.
fn put2(p: [*]const u8, n: usize) isize {
    var q = p;
    var left = n;
    while (left != 0) {
        const w: isize = @bitCast(linux.syscall3(.write, 2, @intFromPtr(q), left));
        if (w <= 0) return -1;
        q += @intCast(w);
        left -= @intCast(w);
    }
    return 0;
}

fn run() u64 {
    const r = linux.syscall6(.mmap, 0, 4096, PROT_RW, MAP_PRIVATE_ANON, NO_FD, 0);
    if (@as(isize, @bitCast(r)) < 0) return 1; // -errno: mmap failed
    const buf: [*]u8 = @ptrFromInt(r);

    // Drain stdin into the arena at offset HDR, accumulating short reads.
    var n: usize = 0;
    while (n < CAP) {
        const got: isize = @bitCast(linux.syscall3(.read, 0, @intFromPtr(buf + HDR + n), CAP - n));
        if (got < 0) return 2;
        if (got == 0) break; // EOF
        n += @intCast(got);
    }

    // The eight hex digits of n as a 32-bit value, most significant first.
    var i: usize = 0;
    while (i < HDR) : (i += 1) {
        const nib: u8 = @intCast((n >> @intCast(4 * (HDR - 1 - i))) & 0xf);
        buf[i] = if (nib < 10) '0' + nib else 'a' + (nib - 10);
    }

    if (put2(buf, HDR + n) != 0) return 3;
    return 0;
}

pub export fn _start() callconv(.c) noreturn {
    const code = run();
    _ = linux.syscall1(.exit, code);
    unreachable;
}
