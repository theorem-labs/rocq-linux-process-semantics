// Target translation of mmap-upper: write argv[1] with 'a'..'z'
// uppercased + '\n' in one write, using one anonymous mmap'd page as
// the buffer, munmapped after the write.  argc < 2 -> exit 2; len >
// 4095 -> exit 3; mmap failure -> exit 4; write error -> exit 5; else
// exit 0.
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
    const s: [*]const u8 = @ptrFromInt(argv[1]);
    const n = slen(s);
    if (n > 4095) return 3;

    const r = linux.syscall6(.mmap, 0, 4096, PROT_RW, MAP_PRIVATE_ANON, NO_FD, 0);
    if (@as(isize, @bitCast(r)) < 0) return 4; // -errno: mmap failed

    const buf: [*]u8 = @ptrFromInt(r);
    var i: usize = 0;
    while (i < n) : (i += 1) {
        const c = s[i];
        buf[i] = if (c >= 'a' and c <= 'z') c - 'a' + 'A' else c;
    }
    buf[n] = '\n';
    if (put(buf, n + 1) != 0) return 5;
    _ = linux.syscall2(.munmap, r, 4096);
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
