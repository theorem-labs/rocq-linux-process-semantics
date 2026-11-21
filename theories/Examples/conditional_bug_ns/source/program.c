/* conditional-bug: dispatch on the FIRST BYTE of argv[1].
     'n' -> exit 0, no output;
     'h' -> write "hello\n", exit 0;
     'o' -> read one byte from unallocated memory (see below);
     any other first byte (or empty argv[1]) -> exit 3 (no output);
     argc < 2 -> exit 2 (no output); write error -> exit 4.
   The 'o' arm is an INTENTIONAL MEMORY-SAFETY BUG on exactly those
   inputs: a volatile load from address 64, far below the image's first
   LOAD segment, so it is unallocated in the model — those runs fault on
   the load, which is deterministic and therefore satisfies the
   all-executions-error source escape in
   Equivalence.equiv.  (Under a real kernel address 64 is unmapped too, so the
   'o' arm segfaults — identically in both binaries.)  The other arms
   are fully defined and straight-line, so the proof mixes ordinary
   simulation with the escape, selected by a single byte of input. */
#include <unistd.h>

static int put(const char *p, unsigned long n) {
    while (n) {
        long w = write(1, p, n);
        if (w <= 0) return -1;
        p += w;
        n -= (unsigned long)w;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 2) return 2;
    char c = argv[1][0];

    if (c == 'n') return 0;
    if (c == 'h') return put("hello\n", 6) ? 4 : 0;
    if (c == 'o') {
        /* BUG: address 64 is not mapped — illegal load in the model */
        unsigned char b = *(volatile const unsigned char *)64;
        (void)b;
        return 0;
    }
    return 3;
}
