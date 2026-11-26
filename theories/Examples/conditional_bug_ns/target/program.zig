// Target translation of conditional-bug: dispatch on the FIRST BYTE of
// argv[1].  'n' -> exit 0, no output; 'h' -> write "hello\n", exit 0;
// 'o' -> volatile load from unallocated address 64 (same intentional
// memory-safety bug as the source: illegal in the model, a segfault
// under a real kernel — identically in both binaries); any other first
// byte -> exit 3; argc < 2 -> exit 2; write error -> exit 4.
const linux = @import("std").os.linux;

const hello: [6]u8 = "hello\n".*;

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

fn run(argc: usize, argv: [*]const usize) u64 {
    if (argc < 2) return 2;
    const s: [*]const u8 = @ptrFromInt(argv[1]);
    const c = s[0];

    if (c == 'n') return 0;
    if (c == 'h') return if (put(&hello, hello.len) != 0) 4 else 0;
    if (c == 'o') {
        // BUG (same as source): address 64 is not mapped — illegal load
        const p: *const volatile u8 = @ptrFromInt(64);
        _ = p.*;
        return 0;
    }
    return 3;
}

pub export fn _start() callconv(.c) noreturn {
    const sp = @frameAddress();
    const stack: [*]const usize = @ptrFromInt(sp);
    const argc = stack[0];
    const code = run(argc, stack + 1);
    _ = linux.syscall1(.exit, code);
    unreachable;
}
