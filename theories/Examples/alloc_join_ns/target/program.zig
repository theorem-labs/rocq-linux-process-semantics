// Target translation of alloc-join: write argv[1..] joined by single
// spaces + '\n' in one write.  THE ALLOCATOR DIFFERS FROM THE SOURCE:
// the source grows the brk heap for its buffer; this target mmaps an
// anonymous region instead.  Neither emits trace events, so the
// observable behavior is identical: argc < 2 -> exit 2; total output
// > 65536 bytes -> exit 3; allocation failure (mmap here, brk in the
// source) -> exit 4; write error -> exit 5; else exit 0, one write of
// the joined string.
const linux = @import("std").os.linux;

const PROT_RW: usize = 3; // PROT_READ | PROT_WRITE
const MAP_PRIVATE_ANON: usize = 0x22; // MAP_PRIVATE | MAP_ANONYMOUS
const NO_FD: usize = @bitCast(@as(isize, -1));

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

    // total = sum of arg lengths + (argc-2) separators + 1 newline
    var total: usize = 0;
    var i: usize = 1;
    while (i < argc) : (i += 1) {
        total += slen(@ptrFromInt(argv[i]));
        if (i > 1) total += 1;
    }
    total += 1;
    if (total > 65536) return 3;

    const r = linux.syscall6(.mmap, 0, total, PROT_RW, MAP_PRIVATE_ANON, NO_FD, 0);
    if (@as(isize, @bitCast(r)) < 0) return 4; // -errno: mmap failed

    const buf: [*]u8 = @ptrFromInt(r);
    var pos: usize = 0;
    i = 1;
    while (i < argc) : (i += 1) {
        if (i > 1) {
            buf[pos] = ' ';
            pos += 1;
        }
        const s: [*]const u8 = @ptrFromInt(argv[i]);
        var j: usize = 0;
        while (s[j] != 0) : (j += 1) {
            buf[pos] = s[j];
            pos += 1;
        }
    }
    buf[pos] = '\n';
    pos += 1;
    if (put(buf, pos) != 0) return 5;
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
