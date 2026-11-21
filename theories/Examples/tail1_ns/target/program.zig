// Target translation of tail-1: read ALL of stdin (to EOF), then write
// only its last line — including its '\n' if the input ends in one,
// the unterminated tail otherwise; empty input writes nothing.
// "a\nb\n" -> "b\n"; "a\nb" -> "b"; "\n" -> "\n"; "" -> "".
// Any line longer than 4096 bytes -> exit 3.  Read error -> exit 1;
// write error -> exit 4; else exit 0.  Arguments ignored.
const linux = @import("std").os.linux;

var rb: [1024]u8 = @splat(0); // read chunk
var cur: [4096]u8 = @splat(0); // unterminated line in progress
var done: [4097]u8 = @splat(0); // last completed line, incl. its '\n'

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
    var cur_n: usize = 0;
    var done_n: usize = 0;

    while (true) {
        const r: isize = @bitCast(linux.syscall3(.read, 0, @intFromPtr(&rb), rb.len));
        if (r < 0) return 1;
        if (r == 0) break;
        var i: usize = 0;
        while (i < @as(usize, @intCast(r))) : (i += 1) {
            const c = rb[i];
            if (c == '\n') {
                var j: usize = 0;
                while (j < cur_n) : (j += 1) done[j] = cur[j];
                done[cur_n] = '\n';
                done_n = cur_n + 1;
                cur_n = 0;
            } else {
                if (cur_n >= cur.len) return 3;
                cur[cur_n] = c;
                cur_n += 1;
            }
        }
    }

    if (cur_n > 0) {
        if (put(&cur, cur_n) != 0) return 4;
    } else if (done_n > 0) {
        if (put(&done, done_n) != 0) return 4;
    }
    return 0;
}

pub export fn _start() callconv(.c) noreturn {
    const code = run();
    _ = linux.syscall1(.exit, code);
    unreachable;
}
