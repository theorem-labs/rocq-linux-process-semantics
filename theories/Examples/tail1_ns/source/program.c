/* tail-1: read ALL of stdin (to EOF), then write only its last line.  A
   line is a maximal run of bytes ending in '\n'; bytes after the last
   '\n' form a final unterminated line.  Output is the last line
   including its '\n' if the input ends in one, the unterminated tail
   otherwise; empty input produces no output.  Examples: "a\nb\n" ->
   "b\n"; "a\nb" -> "b"; "\n" -> "\n"; "" -> "".
   Any line longer than 4096 bytes -> exit 3 (line-buffer cap, no
   output).  Read error -> exit 1; write error -> exit 4.  Success ->
   exit 0.  Arguments are ignored. */
#include <unistd.h>

static char rb[1024];        /* read chunk */
static char cur[4096];       /* unterminated line in progress */
static char done[4097];      /* last completed line, incl. its '\n' */

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
    unsigned long cur_n = 0, done_n = 0;

    for (;;) {
        long r = read(0, rb, sizeof(rb));
        if (r < 0) return 1;
        if (r == 0) break;
        for (long i = 0; i < r; i++) {
            char c = rb[i];
            if (c == '\n') {
                for (unsigned long j = 0; j < cur_n; j++) done[j] = cur[j];
                done[cur_n] = '\n';
                done_n = cur_n + 1;
                cur_n = 0;
            } else {
                if (cur_n >= sizeof(cur)) return 3;
                cur[cur_n++] = c;
            }
        }
    }

    if (cur_n > 0) {
        if (put(cur, cur_n)) return 4;
    } else if (done_n > 0) {
        if (put(done, done_n)) return 4;
    }
    return 0;
}
