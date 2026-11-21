/* headcp: copy the first up-to-128 bytes of file argv[1] into argv[2].
   Unlike cp, there is NO copy loop: a single read of a 128-byte buffer
   followed by a single write of exactly what was read.  File I/O emits
   no trace events — the effect is observable only through the final
   file-system state (out := the first min(128, |argv[1]|) bytes of
   argv[1]'s contents) and the exit code.
   argc < 3 -> exit 2; opening argv[1] fails -> exit 3; creating argv[2]
   fails -> exit 4; read error -> exit 5; short/failed write -> exit 6.
   Success -> exit 0.

   The opens go through the crt's raw_syscall wrapper: opening a missing
   file is a live modeled path (-ENOENT), and musl's open() would convert
   that into an errno write — but errno lives in TLS, which the minimal
   crt never sets up.  The raw calls keep every modeled path errno-free.
   The read/write also go raw: reading a directory fd (-EISDIR) is a
   live modeled error path, and musl's read() would convert it into an
   errno write. */
#include <unistd.h>
#include <fcntl.h>
#include <sys/syscall.h>

long raw_syscall(long nr, long a, long b, long c, long d, long e, long f);

static char buf[128];

int main(int argc, char **argv) {
    if (argc < 3) return 2;

    long in = raw_syscall(SYS_openat, AT_FDCWD, (long)argv[1], O_RDONLY, 0,
                          0, 0);
    if (in < 0) return 3;
    long out = raw_syscall(SYS_openat, AT_FDCWD, (long)argv[2],
                           O_WRONLY | O_CREAT | O_TRUNC, 0644, 0, 0);
    if (out < 0) return 4;

    long r = raw_syscall(SYS_read, in, (long)buf, sizeof(buf), 0, 0, 0);
    if (r < 0) return 5;
    if (raw_syscall(SYS_write, out, (long)buf, r, 0, 0, 0) != r) return 6;

    close((int)in);
    close((int)out);
    return 0;
}
