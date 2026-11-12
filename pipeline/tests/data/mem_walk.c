/* Pointers stored in memory that move: struct fields, globals, pointers
   through a pointer. Each function exercises one shape of PtrIdx's caches
   for memory-resident pointers (pointer_arithmetic_refactor.md Part V). */
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

struct reader {
    const unsigned char *pos;
    const unsigned char *end;
    int line;
};

struct writer {
    char *out;
    size_t written;
};

/* A field advanced in a loop; a different field of the same struct is
   written in the loop (disjoint), so the cache survives. */
int count_lines(struct reader *r) {
    while (r->pos < r->end) {
        if (*r->pos == '\n')
            r->line++;
        r->pos++;
    }
    return r->line;
}

/* Post-increment used as a value: t = r->pos; r->pos = t + 1; *t. */
unsigned sum_bytes(struct reader *r, int n) {
    unsigned s = 0;
    for (int i = 0; i < n && r->pos < r->end; i++)
        s += *r->pos++;
    return s;
}

/* A big-endian u32 at the cursor, then the cursor moves by 4. */
static unsigned read_u32(const unsigned char *p) {
    return (unsigned)p[0] << 24 | (unsigned)p[1] << 16 | (unsigned)p[2] << 8 | p[3];
}

/* The amp_decode_arg shape: a read-only call keeps the cache, malloc keeps
   it, memcpy (opaque) forces a reload. */
char *take_string(struct reader *r) {
    unsigned len = read_u32(r->pos);
    r->pos += 4;
    char *s = malloc(len + 1);
    if (!s)
        return NULL;
    memcpy(s, r->pos, len);
    s[len] = 0;
    r->pos += len;
    return s;
}

/* Pre-increment used as a value, and a store through the cached pointer. */
void put_char(struct writer *w, char c) {
    *w->out = c;
    ++w->out;
    w->written++;
}

void put_string(struct writer *w, const char *s) {
    while (*s)
        *w->out++ = *s++;
}

/* A global cursor. */
static const char *cursor;

void set_cursor(const char *s) { cursor = s; }

int skip_spaces(void) {
    int n = 0;
    while (*cursor == ' ') {
        cursor = cursor + 1;
        n++;
    }
    return n;
}

/* A pointer reached through a pointer: (*pp)++. */
int next_int(const int **pp) {
    int v = **pp;
    (*pp)++;
    return v;
}

/* The cache must be reloaded when the struct pointer changes. */
int total(struct reader *rs, int k) {
    int t = 0;
    for (int i = 0; i < k; i++) {
        struct reader *r = &rs[i];
        while (r->pos < r->end) {
            t += *r->pos;
            r->pos += 1;
        }
    }
    return t;
}

/* A rebase store (not derived from the old value) followed by moves. */
int rewind_and_count(struct reader *r, const unsigned char *start) {
    int n = 0;
    r->pos = start;
    while (r->pos != r->end) {
        r->pos += 2;
        n++;
        if (r->end - r->pos < 2)
            break;
    }
    return n;
}
