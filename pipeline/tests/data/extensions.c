/* Every GNU / C23 extension that c2r/rewrite.py removes, in a program whose
   output must not change when they are rewritten. */
#include <stdio.h>
#include <string.h>

struct point { int x, y; };

static int classify(int c) {
    switch (c) {
    case '0' ... '9': return 1;
    case 'a' ... 'f': return 2;
    case 110 ... 113: return 3;
    case -3 ... -1: return 4;
    default:
    }
    return 0;
}

static unsigned sum_bytes(const void *buf, int n) {
    unsigned s = 0;
    const void *end = buf + n;
    for (const void *p = buf; p != end; p++)
        s += *(const unsigned char *)p;
    return s;
}

static long distance(void *a, void *b) { return b - a; }

static void *advance(void *p, int n) {
    p += n;
    return 2 + p;
}

static void first_negative(const int *v, int n, int *at) {
    for (*at = 0; *at < n; ++*at)
        if (v[*at] < 0)
            goto out;
    *at = -1;
out:
}

int main(void) {
    unsigned mask = 0b1010u;
    double g = 9.81d;
    struct point origin = {};
    struct point q = (struct point){};
    int grid[2][3] = { {}, {1, 2, 3} };
    char text[] = "pointer arithmetic";
    int v[] = {3, 1, -4, 1};
    char *base = text;

    printf("%u %.2f %d %d %d %d\n", mask, g, origin.x, q.y, grid[0][2], grid[1][2]);
    for (int c = -4; c < 120; c += 3)
        printf("%d", classify(c));
    printf(" %d%d\n", classify('7'), classify('c'));
    printf("%u %ld\n", sum_bytes(text, (int)strlen(text)), distance(text, text + 7));
    printf("%s\n", (char *)advance(base, 3));
    printf("%d %d %d\n", __builtin_popcount(0xF0F0u), __builtin_parity(7), __builtin_popcountll(~0ULL));
    printf("%d\n", (int)__builtin_strlen(text));
    int at;
    first_negative(v, 4, &at);
    printf("%d\n", at);
    return 0;
}
