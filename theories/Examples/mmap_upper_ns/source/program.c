/* mmap-upper: write argv[1] with ASCII 'a'..'z' uppercased, followed by
   '\n', in one write.  The output buffer is one anonymous page from
   mmap, unmapped again after the write.  argc < 2 -> exit 2 (no output);
   strlen(argv[1]) > 4095 -> exit 3 (must fit the page with the trailing
   '\n', no output); mmap failure -> exit 4 (no output); write error ->
   exit 5.  Success -> exit 0.

   mmap/munmap go through the crt's raw_syscall wrapper: the model lets
   mmap fail with any errno, and musl's wrapper converts that into an
   errno write — but errno lives in TLS, which the minimal crt never
   sets up.  The raw calls keep every modeled path errno-free. */
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
    if (n > 4095) return 3;

    /* PROT_READ|PROT_WRITE = 3, MAP_PRIVATE|MAP_ANONYMOUS = 0x22 */
    long r = raw_syscall(SYS_mmap, 0, 4096, 3, 0x22, -1, 0);
    if (r < 0) return 4;                /* -errno: mmap failed */
    char *buf = (char *)r;

    for (unsigned long i = 0; i < n; i++) {
        char c = s[i];
        buf[i] = (c >= 'a' && c <= 'z') ? (char)(c - 'a' + 'A') : c;
    }
    buf[n] = '\n';
    if (put(buf, n + 1)) return 5;
    raw_syscall(SYS_munmap, r, 4096, 0, 0, 0, 0);
    return 0;
}
