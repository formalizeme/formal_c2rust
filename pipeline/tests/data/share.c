/* Base sharing decided by liveness (pointer_arithmetic_refactor.md §7),
   and comparisons and differences done on indices (§8.3). */
#include <stdio.h>
#include <string.h>

static const char *lines[] = { "alpha", "be", "gamma delta", "", "x", NULL };
static int pos;

static const char *next_line(void) { return lines[pos] ? lines[pos++] : NULL; }

/* line is rebased in every iteration (a call result); s is a copy of it
   that is dead at the rebase, so both share one base, and s - line is an
   index difference. */
size_t longest(void) {
    size_t best = 0;
    const char *line;
    pos = 0;
    while ((line = next_line()) != NULL) {
        const char *s = line;
        while (*s)
            s++;
        if ((size_t)(s - line) > best)
            best = (size_t)(s - line);
    }
    return best;
}

/* p is rebased by strchr while start is still live: they must not share a
   base. */
int field_widths(const char *s) {
    const char *start = s, *p;
    int out = 0;
    while ((p = strchr(start, ',')) != NULL) {
        out = out * 10 + (int)(p - start);
        start = p + 1;
    }
    return out * 10 + (int)strlen(start);
}

/* One source (the parameter): p and end share buf's base, so p != end
   compares indices. */
size_t count_char(const char *buf, size_t n, char c) {
    const char *p = buf, *end = buf + n;
    size_t k = 0;
    for (; p != end; p++)
        if (*p == c)
            k++;
    return k + (size_t)(end - buf) * 1000;
}

/* A loop made of goto: w is rebased by strchr each round while s is still
   live (strlen(s), w - s): no shared base. */
int words(const char *text) {
    const char *s = text, *w;
    int n = 0;
again:
    w = strchr(s, ' ');
    if (w == NULL)
        return n * 100 + (int)strlen(s);
    n += (int)(w - s);
    s = w + 1;
    goto again;
}

/* A loop made of goto in which sharing is safe: t is rebased each round
   while e is dead, so e - t is an index difference. */
int token_lengths(void) {
    const char *t, *e;
    int n = 0;
    pos = 0;
again:
    t = next_line();
    if (t == NULL)
        return n;
    e = t;
    while (*e)
        e++;
    n = n * 10 + (int)(e - t);
    goto again;
}

/* Elements larger than one byte: comparisons stay on pointers. */
int count_ints(const int *v, const int *end, int x) {
    int k = 0;
    for (; v != end; v++)
        if (*v == x)
            k++;
    return k;
}

int main(void) {
    printf("longest %zu\n", longest());
    printf("widths %d\n", field_widths("ab,,cde,f,ghij"));
    printf("count %zu\n", count_char("banana bread", 12, 'a'));
    printf("words %d\n", words("one two  three"));
    printf("tokens %d\n", token_lengths());
    int v[] = { 3, 1, 3, 3, 2 };
    printf("ints %d\n", count_ints(v, v + 5, 3));
    return 0;
}
