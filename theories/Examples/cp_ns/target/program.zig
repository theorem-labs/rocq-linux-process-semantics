// Target translation of cp: copy the file argv[1] to argv[2] through a
// 1024-byte buffer — openat(argv[1], O_RDONLY), openat(argv[2],
// O_WRONLY|O_CREAT|O_TRUNC, 0644), read/write to EOF, close both.
// File I/O emits no trace events; the copy is observed in the final
// file-system state.  argc < 3 -> exit 2; open argv[1] fails -> exit 3;
// create argv[2] fails -> exit 4; read error -> exit 5; write error ->
// exit 6; else exit 0.
//
// An over-PATH_MAX path needs no special handling here: openat returns
// -ENAMETOOLONG for it (Specs.openat_spec, as Linux's getname() does),
// so a path of length >= 4096 in argv[1] exits 3 and one in argv[2]
// exits 4 through the ordinary open-failed branches — exactly what the
// C source does.  Earlier revisions carried a defensive guard that
// exited 3 whenever strlen(argv[2]) >= 4096, because the model then
// ERRORED on such a path instead of answering an errno; with the errno
// modeled, that guard would make this target disagree with the source
// (which exits 4).
const linux = @import("std").os.linux;

const AT_FDCWD: usize = @bitCast(@as(isize, -100));
const O_RDONLY: usize = 0;
const O_WR_CREATE_TRUNC: usize = 1 + 64 + 512; // O_WRONLY | O_CREAT | O_TRUNC

var buf: [1024]u8 = @splat(0);

fn run(argc: usize, argv: [*]const usize) u64 {
    if (argc < 3) return 2;

    const in: isize = @bitCast(linux.syscall4(.openat, AT_FDCWD, argv[1], O_RDONLY, 0));
    if (in < 0) return 3;
    const out: isize = @bitCast(linux.syscall4(.openat, AT_FDCWD, argv[2], O_WR_CREATE_TRUNC, 0o644));
    if (out < 0) return 4;

    const infd: usize = @intCast(in);
    const outfd: usize = @intCast(out);
    while (true) {
        const r: isize = @bitCast(linux.syscall3(.read, infd, @intFromPtr(&buf), buf.len));
        if (r < 0) return 5;
        if (r == 0) break;
        var p: [*]const u8 = &buf;
        var left: usize = @intCast(r);
        while (left != 0) {
            const w: isize = @bitCast(linux.syscall3(.write, outfd, @intFromPtr(p), left));
            if (w <= 0) return 6;
            p += @intCast(w);
            left -= @intCast(w);
        }
    }

    _ = linux.syscall1(.close, infd);
    _ = linux.syscall1(.close, outfd);
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
