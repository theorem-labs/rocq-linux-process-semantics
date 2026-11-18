/* alloc-join: write argv[1..argc-1] joined by single spaces, followed by
   '\n', in one write.  The output buffer is allocated with the brk
   syscall HERE IN THE SOURCE; the target allocates the same buffer with
   mmap instead.  Neither allocator emits trace events, so the observable
   behavior (one write of the joined string, same exit codes) is
   identical — the point of this example is that the allocation method is
   free to differ between the two binaries.
   argc < 2 -> exit 2 (no output); total output longer than 65536 bytes ->
   exit 3 (no output); allocation failure (brk(0) returning 0, address
   wraparound, or the kernel refusing the grow — mmap failure in the
   target) -> exit 4 (no output); write error -> exit 5.  Success ->
   exit 0.

   brk goes through the crt's raw_syscall wrapper: musl's brk()/sbrk()
   are stubs, and musl's syscall() converts error-range returns into an
   errno write — but errno lives in TLS, which the minimal crt never
   sets up, and the model lets brk(0) report any 64-bit value.  The raw
   call keeps every modeled path errno-free. */
#include <unistd.h>
#include <sys/syscall.h>

long raw_syscall(long nr, long a, long b, long c, long d, long e, long f);

static int put(const char *p, unsigned long n) {
    while (n) {
        long w = write(1, p, n);
        if (w <= 0) return -1;
        p += w;
        n -= (unsigned long)w;
    }
    return 0;
}

static unsigned long slen(const char *s) {
    unsigned long n = 0;
    while (s[n]) n++;
    return n;
}

int main(int argc, char **argv) {
    if (argc < 2) return 2;

    /* total = sum of arg lengths + (argc-2) separators + 1 newline */
    unsigned long total = 0;
    for (int i = 1; i < argc; i++) {
        total += slen(argv[i]);
        if (i > 1) total++;
    }
    total++;
    if (total > 65536) return 3;

    unsigned long cur = (unsigned long)raw_syscall(SYS_brk, 0, 0, 0, 0, 0, 0);
    if (cur == 0) return 4;
    unsigned long want = cur + total;
    if (want <= cur) return 4;          /* address wraparound */
    unsigned long got =
        (unsigned long)raw_syscall(SYS_brk, (long)want, 0, 0, 0, 0, 0);
    if (got != want) return 4;          /* kernel kept the old break */

    char *buf = (char *)cur;
    unsigned long pos = 0;
    for (int i = 1; i < argc; i++) {
        if (i > 1) buf[pos++] = ' ';
        const char *s = argv[i];
        for (unsigned long j = 0; s[j]; j++) buf[pos++] = s[j];
    }
    buf[pos++] = '\n';
    if (put(buf, pos)) return 5;
    return 0;
}
