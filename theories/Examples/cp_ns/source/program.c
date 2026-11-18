/* cp: copy the file argv[1] to argv[2] through a 1024-byte buffer: open
   argv[1] read-only, create-or-truncate argv[2], read/write until EOF,
   close both.  File I/O emits no trace events — the copy is observable
   only through the final file-system state (and the exit code).
   argc < 3 -> exit 2; opening argv[1] fails -> exit 3; creating argv[2]
   fails -> exit 4; read error -> exit 5; write error -> exit 6.
   Success -> exit 0.

   The opens and the copy-loop I/O go through the crt's raw_syscall
   wrapper: opening a missing file (-ENOENT) and reading a directory
   fd (-EISDIR) are live modeled paths, and musl's open()/read()
   convert those into an errno write — but errno lives in TLS, which
   the minimal crt never sets up.  The raw calls keep every modeled
   path errno-free. */
#include <unistd.h>
#include <fcntl.h>
#include <sys/syscall.h>

long raw_syscall(long nr, long a, long b, long c, long d, long e, long f);

static char buf[1024];

int main(int argc, char **argv) {
    if (argc < 3) return 2;

    long in = raw_syscall(SYS_openat, AT_FDCWD, (long)argv[1], O_RDONLY, 0,
                          0, 0);
    if (in < 0) return 3;
    long out = raw_syscall(SYS_openat, AT_FDCWD, (long)argv[2],
                           O_WRONLY | O_CREAT | O_TRUNC, 0644, 0, 0);
    if (out < 0) return 4;

    for (;;) {
        long r = raw_syscall(SYS_read, in, (long)buf, sizeof(buf), 0, 0, 0);
        if (r < 0) return 5;
        if (r == 0) break;
        const char *p = buf;
        unsigned long n = (unsigned long)r;
        while (n) {
            long w = raw_syscall(SYS_write, out, (long)p, (long)n, 0, 0, 0);
            if (w <= 0) return 6;
            p += w;
            n -= (unsigned long)w;
        }
    }

    close((int)in);
    close((int)out);
    return 0;
}
