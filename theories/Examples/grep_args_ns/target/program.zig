// Target translation of grep-args: for each argv[i>=2] that contains the
// substring argv[1], write that argv[i] followed by '\n'.  argc < 2 ->
// exit 2 (no output).  Empty pattern matches every arg.  A write error
// (write result <= 0) -> exit 3 immediately.  Otherwise exit 0.
const linux = @import("std").os.linux;

const newline: [1]u8 = .{'\n'};

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

// 1 if needle occurs in hay, else 0.  Empty needle matches.  Same
// O(n*m) scan as the source.
fn contains(hay: [*]const u8, needle: [*]const u8) bool {
    const hn = slen(hay);
    const nn = slen(needle);
    if (nn == 0) return true;
    if (nn > hn) return false;
    var i: usize = 0;
    while (i + nn <= hn) : (i += 1) {
        var j: usize = 0;
        while (j < nn and hay[i + j] == needle[j]) j += 1;
        if (j == nn) return true;
    }
    return false;
}

fn run(argc: usize, argv: [*]const usize) u64 {
    if (argc < 2) return 2;
    const pat: [*]const u8 = @ptrFromInt(argv[1]);
    var i: usize = 2;
    while (i < argc) : (i += 1) {
        const s: [*]const u8 = @ptrFromInt(argv[i]);
        if (contains(s, pat)) {
            if (put(s, slen(s)) != 0) return 3;
            if (put(&newline, 1) != 0) return 3;
        }
    }
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
