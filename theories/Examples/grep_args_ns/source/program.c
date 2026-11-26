/* grep-args: for each argv[i>=2] that contains the substring argv[1], write
   that argv[i] followed by '\n'. Args not containing the pattern produce no
   output. argc<2 -> exit 2 (no output). An empty pattern (argv[1] == "")
   matches every arg (it is a substring of any string). Substring search is a
   manual O(n*m) scan with explicit bounds; raw write only; fully total. */
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

static unsigned long slen(const char *s) {
    unsigned long n = 0;
    while (s[n]) n++;
    return n;
}

/* 1 if needle occurs in hay, else 0. Empty needle -> 1. */
static int contains(const char *hay, const char *needle) {
    unsigned long hn = slen(hay), nn = slen(needle);
    if (nn == 0) return 1;
    if (nn > hn) return 0;
    for (unsigned long i = 0; i + nn <= hn; i++) {
        unsigned long j = 0;
        while (j < nn && hay[i + j] == needle[j]) j++;
        if (j == nn) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 2) return 2;

    const char *pat = argv[1];
    for (int i = 2; i < argc; i++) {
        if (contains(argv[i], pat)) {
            if (put(argv[i], slen(argv[i]))) return 3;
            if (put("\n", 1)) return 3;
        }
    }
    return 0;
}
