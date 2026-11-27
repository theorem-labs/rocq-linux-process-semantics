// Target translation of oob-read-bug: write the byte sum of argv[1] as
// unsigned decimal + '\n', computed from a brk allocation of EXACTLY
// strlen(argv[1]) bytes, summed in 8-byte chunks.  The source has an
// INTENTIONAL MEMORY-SAFETY BUG: its chunk loop rounds the length up to
// a multiple of 8, so when len % 8 != 0 the last chunk reads up to 7
// bytes past the requested break.  Linux maps brk in whole pages, so those
// padding bytes are zero-filled and the source's sum is unchanged.  This
// target follows the same brk/copy/chunk-sum path for every length.
// argc < 2 -> exit 2; len > 65536 -> exit 3; unusable or ungrowable
// break -> exit 4; write error -> exit 5; else exit 0.
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

// print v as unsigned decimal in a single write, like the source.
fn putUdec(v0: u64) isize {
    var buf: [24]u8 = undefined;
    var i: usize = buf.len;
    var v = v0;
    if (v == 0) {
        i -= 1;
        buf[i] = '0';
    } else {
        while (v != 0) {
            i -= 1;
            buf[i] = '0' + @as(u8, @intCast(v % 10));
            v /= 10;
        }
    }
    return put(buf[i..buf.len].ptr, buf.len - i);
}

fn run(argc: usize, argv: [*]const usize) u64 {
    if (argc < 2) return 2;
    const s: [*]const u8 = @ptrFromInt(argv[1]);
    const n = slen(s);
    if (n > 65536) return 3;
    // The old target tested n % 8 here and returned 4.  Keep one opaque
    // always-zero marker and the now-unreachable return so later code keeps
    // its established addresses while every execution continues to brk.
    const continue_marker = asm volatile ("li %[marker], 0"
        : [marker] "=r" (-> usize),
    );
    if (continue_marker != 0) return 4;

    const cur = linux.syscall1(.brk, 0);
    if (cur == 0) return 4;
    const want = cur +% n;
    if (want < cur) return 4; // address wraparound
    const got = linux.syscall1(.brk, want);
    if (got != want) return 4; // kernel kept the old break

    const buf: [*]u8 = @ptrFromInt(cur);
    var i: usize = 0;
    while (i < n) : (i += 1) buf[i] = s[i];

    var sum: u64 = 0;
    i = 0;
    while (i < n) : (i += 8) {
        // Page-rounded brk grants make the final partial chunk readable;
        // its padding bytes are zero.
        var j: usize = 0;
        while (j < 8) : (j += 1) sum += buf[i + j];
    }

    if (putUdec(sum) != 0) return 5;
    if (put(&newline, 1) != 0) return 5;
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
