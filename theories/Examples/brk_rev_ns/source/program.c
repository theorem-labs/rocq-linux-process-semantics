/* brk-rev: write argv[1] reversed, followed by '\n', in one write.  The
   output buffer is allocated with the brk syscall: query the current break
   with brk(0), then grow it by len+1 bytes and use the granted
   (zero-filled) region.  Every environment choice is handled with a
   defined exit: argc < 2 -> exit 2 (no output); strlen(argv[1]) > 65536 ->
   exit 3 (buffer cap, no output); an unusable or ungrowable break (brk(0)
   returning 0 or an address so high the request wraps, or the kernel
   refusing the grow) -> exit 4 (no output); write error -> exit 5.
   Success -> exit 0.

   brk goes through the crt's raw_syscall wrapper: musl's public
   brk()/sbrk() are stubs, and even musl's syscall() converts
   error-range return values into an errno write — but errno lives in
   TLS, which the minimal crt never sets up, and the model lets brk(0)
   report any 64-bit value.  The raw call keeps every modeled path
   errno-free. */
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
    const char *s = argv[1];
    unsigned long n = slen(s);
    if (n > 65536) return 3;

    unsigned long cur = (unsigned long)raw_syscall(SYS_brk, 0, 0, 0, 0, 0, 0);
    if (cur == 0) return 4;
    unsigned long want = cur + n + 1;
    if (want <= cur) return 4;          /* address wraparound */
    unsigned long got =
        (unsigned long)raw_syscall(SYS_brk, (long)want, 0, 0, 0, 0, 0);
    if (got != want) return 4;          /* kernel kept the old break */

    char *buf = (char *)cur;
    for (unsigned long i = 0; i < n; i++) buf[i] = s[n - 1 - i];
    buf[n] = '\n';
    if (put(buf, n + 1)) return 5;
    return 0;
}
