/* cat-1024: copy stdin to stdout through a 1024-byte buffer.  Reads until
   EOF (read returning 0, sticky thereafter); each chunk is written fully
   before the next read.  Short reads are passed through as-is — the
   model's byte-level trace events erase chunking anyway.  Arguments are
   ignored.  Read error -> exit 1; write error -> exit 2; EOF -> exit 0. */
#include <unistd.h>

static char buf[1024];

static int put(const char *p, unsigned long n) {
    while (n) {
        long w = write(1, p, n);
        if (w <= 0) return -1;
        p += w;
        n -= (unsigned long)w;
    }
    return 0;
}

int main(void) {
    for (;;) {
        long r = read(0, buf, sizeof(buf));
        if (r == 0) return 0;
        if (r < 0) return 1;
        if (put(buf, (unsigned long)r)) return 2;
    }
}
