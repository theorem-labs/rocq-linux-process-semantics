// Target translation of modprint: print argc modulo a runtime-loaded
// divisor as one decimal digit followed by a newline, then exit 0.
// Straight-line, no input-dependent control flow — see the source's
// program.c for the full description, including why the load of
// modulus_base must stay volatile in both binaries.
const linux = @import("std").os.linux;

// .bss: four zero bytes in the loaded image.
var modulus_base: i32 = 0;

// .data: the output buffer, patched in place with the rendered digit.
var out: [2]u8 = .{ '0', '\n' };

fn run(argc: u64) u64 {
    // volatile, for the same reason as the source: without it the
    // divisor folds to a constant and the remu disappears.
    const p: *const volatile i32 = &modulus_base;
    const d: u64 = @intCast(p.* + 7);
    const r: u64 = argc % d;
    out[0] = @intCast('0' + r);
    _ = linux.syscall3(.write, 1, @intFromPtr(&out), 2);
    return 0;
}

pub export fn _start() callconv(.c) noreturn {
    const sp = @frameAddress();
    const stack: [*]const usize = @ptrFromInt(sp);
    const argc = stack[0];
    const code = run(argc);
    _ = linux.syscall1(.exit, code);
    unreachable;
}
