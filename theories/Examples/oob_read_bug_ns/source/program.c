/* oob-read-bug: write the sum of the bytes of argv[1] as unsigned decimal,
   followed by '\n'.  The string is copied into a brk allocation of EXACTLY
   strlen(argv[1]) bytes and summed in 8-byte chunks.

   INTENTIONALLY MEMORY-UNSAFE on some inputs: the chunk loop rounds the
   length UP to a multiple of 8, so whenever strlen(argv[1]) % 8 != 0 the
   last chunk reads up to 7 bytes PAST the end of the allocation — a read
   beyond the logical allocation.  Linux and the model map brk memory in
   whole pages, so the trailing bytes of the freshly granted page read as
   zeros and the sum is unchanged.  The target follows the same path for
   every length.  Inputs with length a multiple of 8 (including "") do not
   read the zero padding.

   argc < 2 -> exit 2 (no output); strlen(argv[1]) > 65536 -> exit 3
   (buffer cap, no output); an unusable or ungrowable break -> exit 4
   (no output); write error -> exit 5.  Success -> exit 0.

   brk goes through the crt's raw_syscall wrapper: musl's brk()/sbrk()
   are stubs, and musl's syscall() converts error-range returns into an
   errno write — but errno lives in TLS, which the minimal crt never
   sets up, and the model lets brk(0) report any 64-bit value. */
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

/* print v as unsigned decimal in a single write. */
static int put_udec(unsigned long v) {
    char buf[24];
    int i = sizeof(buf);
    if (v == 0) {
        buf[--i] = '0';
    } else {
        while (v) { buf[--i] = (char)('0' + (int)(v % 10)); v /= 10; }
    }
    return put(&buf[i], (unsigned long)(sizeof(buf) - i));
}

int main(int argc, char **argv) {
    if (argc < 2) return 2;
    const char *s = argv[1];
    unsigned long n = slen(s);
    if (n > 65536) return 3;

    unsigned long cur = (unsigned long)raw_syscall(SYS_brk, 0, 0, 0, 0, 0, 0);
    if (cur == 0) return 4;
    unsigned long want = cur + n;
    if (want < cur) return 4;           /* address wraparound */
    unsigned long got =
        (unsigned long)raw_syscall(SYS_brk, (long)want, 0, 0, 0, 0, 0);
    if (got != want) return 4;          /* kernel kept the old break */

    unsigned char *buf = (unsigned char *)cur;
    for (unsigned long i = 0; i < n; i++) buf[i] = (unsigned char)s[i];

    unsigned long sum = 0;
    for (unsigned long i = 0; i < n; i += 8) {
        /* BUG: when n % 8 != 0 the last chunk reads past the allocation */
        for (unsigned long j = 0; j < 8; j++) sum += buf[i + j];
    }

    if (put_udec(sum)) return 5;
    if (put("\n", 1)) return 5;
    return 0;
}
