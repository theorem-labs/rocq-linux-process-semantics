// Target translation of brk-rev: write argv[1] reversed + '\n' in one
// write, using a brk-allocated buffer (brk(0) query, then grow by
// len+1).  argc < 2 -> exit 2; len > 65536 -> exit 3; unusable or
// ungrowable break (brk(0) = 0, wraparound, grow refused) -> exit 4;
// write error -> exit 5; else exit 0.  Same raw-brk protocol as the
// source, byte for byte the same output.
const linux = @import("std").os.linux;

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

fn slen(s: [*]const u8) usize {
    var n: usize = 0;
    while (s[n] != 0) n += 1;
    return n;
}

fn run(argc: usize, argv: [*]const usize) u64 {
    if (argc < 2) return 2;
    const s: [*]const u8 = @ptrFromInt(argv[1]);
    const n = slen(s);
    if (n > 65536) return 3;

    const cur = linux.syscall1(.brk, 0);
    if (cur == 0) return 4;
    const want = cur +% n +% 1;
    if (want <= cur) return 4; // address wraparound
    const got = linux.syscall1(.brk, want);
    if (got != want) return 4; // kernel kept the old break

    const buf: [*]u8 = @ptrFromInt(cur);
    var i: usize = 0;
    while (i < n) : (i += 1) buf[i] = s[n - 1 - i];
    buf[n] = '\n';
    if (put(buf, n + 1) != 0) return 5;
    return 0;
}

pub export fn _start() callconv(.c) noreturn {
    const sp = @frameAddress();
    const stack: [*]const usize = @ptrFromInt(sp);
    const argc = stack[0];
    const code = run(argc, stack + 1);
    _ = linux.syscall1(.exit, code);
    unreachable;
}
