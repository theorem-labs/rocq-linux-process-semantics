/* arena-tee: drain stdin into an anonymous mmap arena, then write a
   fixed-width hex byte count followed by the drained bytes to STDERR.

   Output is exactly 8 + n bytes on channel 2: eight lowercase hex digits
   holding n zero-padded to 32 bits, immediately followed by the n bytes
   read from stdin.  n is capped at CAP, so a longer stdin is truncated
   (the remainder is left unread, which the model observes as nothing).

   mmap failure -> exit 1 (no output); read error -> exit 2; write error
   -> exit 3; otherwise exit 0.  Arguments are ignored.

   This example exists to exercise the binary-agnostic infrastructure that
   would otherwise have no user in the tree, so its shape is deliberate:

     - the arena is an mmap grant, and BOTH the drain (read's buffer) and
       the header (two word stores) write into it, which is the
       read-buffer-writability and store-into-a-grant reasoning in
       Common/StoreOk.v and CatExec.rdn_wbytes_out;
     - the drain is a bounded read(0,...) loop, which is the shape rule in
       Common/DrainAlg.v;
     - the output goes to fd 2, not fd 1, which is what needs CatSim
       generalized over the output channel rather than pinned to stdout.

   There is exactly ONE data-dependent loop, the drain.  The header digits
   are a constant-trip loop and the emit is a single write, so everything
   after the drain is straight-line and steps reflectively.  An in-place
   transform pass over the arena was deliberately left out: it is where the
   proof cost of the mined pilots actually went, and it covers nothing that
   the drain and the header stores do not already cover.

   mmap goes through the crt's raw_syscall wrapper rather than a musl
   wrapper: the model lets mmap fail with any errno, and musl's wrapper
   turns that into an errno write, but errno lives in TLS that this
   minimal crt never sets up.  See ../crt/_start.S. */
#include <unistd.h>
#include <sys/syscall.h>

long raw_syscall(long nr, long a, long b, long c, long d, long e, long f);

#define HDR 8UL   /* eight hex digits, no separator */
#define CAP 4088UL /* 4096 - HDR: the arena is exactly one page */

/* The four hex digits of v starting at nibble [shift], packed little-endian
   into a word so the caller can store them with a single sw: byte i of the
   result is the digit for nibble shift+4*(3-i). */
static unsigned int hexword(unsigned long v, unsigned int shift) {
    unsigned int w = 0;
    for (unsigned int i = 0; i < 4; i++) {
        unsigned int nib = (unsigned int)((v >> (shift + 4 * (3 - i))) & 0xf);
        unsigned int ch = nib < 10 ? '0' + nib : 'a' + (nib - 10);
        w |= ch << (8 * i);
    }
    return w;
}

static int put2(const char *p, unsigned long n) {
    while (n) {
        long w = write(2, p, n);
        if (w <= 0) return -1;
        p += w;
        n -= (unsigned long)w;
    }
    return 0;
}

int main(void) {
    /* PROT_READ|PROT_WRITE = 3, MAP_PRIVATE|MAP_ANONYMOUS = 0x22 */
    long r = raw_syscall(SYS_mmap, 0, 4096, 3, 0x22, -1, 0);
    if (r < 0) return 1;                /* -errno: mmap failed */
    char *buf = (char *)r;

    unsigned long n = 0;
    while (n < CAP) {
        long got = read(0, buf + HDR + n, CAP - n);
        if (got < 0) return 2;
        if (got == 0) break;            /* EOF */
        n += (unsigned long)got;
    }

    /* Two word stores into the grant, at the page-aligned base and base+4. */
    *(unsigned int *)(buf + 0) = hexword(n, 16);
    *(unsigned int *)(buf + 4) = hexword(n, 0);

    if (put2(buf, HDR + n)) return 3;
    return 0;
}
