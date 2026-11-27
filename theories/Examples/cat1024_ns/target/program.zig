// Target translation of cat-1024: copy stdin to stdout through a
// 1024-byte buffer until EOF (read returning 0).  Each chunk is
// written fully before the next read; short reads pass through as-is.
// Arguments ignored.  Read error -> exit 1; write error -> exit 2;
// EOF -> exit 0.
const linux = @import("std").os.linux;

var buf: [1024]u8 = @splat(0);

// write all n bytes to stdout; -1 on write error, like the source.
fn put(p: [*]const u8, n: usize) isize {
    var q = p;
    var left = n;
    while (left != 0) {
        const w: isize = @bitCast(linux.syscall3(.write, 1, @intFromPtr(q), left));
        if (w <= 0) return -1;
        q += @intCast(w);
        left -= @intCast(w);
    }
    return 0;
}

fn run() u64 {
    while (true) {
        const r: isize = @bitCast(linux.syscall3(.read, 0, @intFromPtr(&buf), buf.len));
        if (r == 0) return 0;
        if (r < 0) return 1;
        if (put(&buf, @intCast(r)) != 0) return 2;
    }
}

pub export fn _start() callconv(.c) noreturn {
    const code = run();
    _ = linux.syscall1(.exit, code);
    unreachable;
}
