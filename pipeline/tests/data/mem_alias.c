/* Cases where a stale cache for a pointer stored in memory would compute a
   different result: stores that overwrite the cached field, callees that move
   it, unions, goto, switch fallthrough, pointers through pointers. Built with
   gcc from this file, and with CompCert from its Clight before and after the
   refactoring; all three must print the same thing. */
#include <stdint.h>
#include <stdio.h>

struct cursor {
    unsigned char *p;
    unsigned char buf[16];
};

/* p points at its own storage; the store through p overwrites p's low byte,
   so the next p++ must read p from memory again. The struct is 256-aligned,
   so the new low byte makes p point at buf[3]. */
static struct cursor self __attribute__((aligned(256)));

int clobber(struct cursor *s) {
    s->p = (unsigned char *)&s->p;
    *s->p = (unsigned char)(uintptr_t)&s->buf[3];
    s->p++;
    return (int)(s->p - (unsigned char *)s);
}

struct reader {
    const char *pos;
    const char *end;
};

/* A callee that moves the field: the caller's cache must not survive it. */
static void skip2(struct reader *r) { r->pos += 2; }

/* A read-only callee: the cache may survive it. */
static int peek(const struct reader *r) { return *r->pos; }

int walk_with_calls(struct reader *r) {
    int n = 0;
    while (r->pos < r->end) {
        if (peek(r) == 'x')
            skip2(r);
        else
            r->pos++;
        n++;
    }
    return n;
}

/* The same through a function pointer. */
int walk_indirect(struct reader *r, void (*step)(struct reader *)) {
    int n = 0;
    while (r->pos < r->end) {
        step(r);
        r->pos++;
        n++;
    }
    return n;
}

static void nothing(struct reader *r) { (void)r; }

/* Two moving fields of one struct: disjoint, both cached. */
int is_palindrome(struct reader *r) {
    r->end--;
    while (r->pos < r->end) {
        if (*r->pos != *r->end)
            return 0;
        r->pos++;
        r->end--;
    }
    return 1;
}

/* A union: the integer member overlaps the pointer member. */
union punned {
    unsigned char *p;
    uintptr_t u;
};

int union_walk(union punned *x, unsigned char *base) {
    x->p = base;
    x->p++;
    x->u += 1;
    x->p++;
    return (int)(x->p - base);
}

/* goto back into the middle of a loop. */
int goto_walk(struct reader *r) {
    int n = 0;
again:
    while (r->pos < r->end) {
        if (*r->pos == ',') {
            r->pos++;
            n += 100;
            goto again;
        }
        r->pos++;
        n++;
    }
    return n;
}

/* switch with fallthrough, moving the field in several cases. */
int switch_walk(struct reader *r) {
    int n = 0;
    while (r->pos < r->end) {
        switch (*r->pos) {
        case 'a':
            r->pos++;
            /* fall through */
        case 'b':
            r->pos++;
            n += 10;
            break;
        case 'c':
            r->pos += 3;
            continue;
        default:
            r->pos++;
        }
        n++;
    }
    return n;
}

/* A global cursor also reached through a pointer to it. */
static const char *gcur;

int global_through_pointer(const char *s) {
    const char **pp = &gcur;
    gcur = s;
    gcur++;
    (*pp)++;
    gcur++;
    return (int)(gcur - s);
}

/* A local struct whose address is passed to a callee that moves the field. */
int local_struct(const char *s, int n) {
    struct reader r = { s, s + n };
    int k = 0;
    while (r.pos < r.end) {
        if (k % 3 == 2)
            skip2(&r);
        r.pos++;
        k++;
    }
    return k * 100 + (int)(r.pos - s);
}

/* Postfix in a condition, and continue. */
int count_until_space(struct reader *r) {
    int n = 0;
    while (r->pos < r->end && *r->pos++ != ' ') {
        if (n > 50)
            continue;
        n++;
    }
    return n;
}

int main(void) {
    printf("clobber %d\n", clobber(&self));

    const char *t = "abxcdxxe";
    struct reader r = { t, t + 8 };
    printf("calls %d", walk_with_calls(&r));
    printf(" offset %d\n", (int)(r.pos - t));

    r.pos = t;
    printf("indirect %d", walk_indirect(&r, skip2));
    r.pos = t;
    printf(" %d", walk_indirect(&r, nothing));
    printf(" offset %d\n", (int)(r.pos - t));

    const char *pal = "racecar", *notpal = "racebar";
    struct reader a = { pal, pal + 7 }, b = { notpal, notpal + 7 };
    printf("palindrome %d %d\n", is_palindrome(&a), is_palindrome(&b));

    unsigned char bytes[8];
    union punned x;
    printf("union %d\n", union_walk(&x, bytes));

    const char *csv = "ab,c,,def";
    struct reader g = { csv, csv + 9 };
    printf("goto %d\n", goto_walk(&g));

    const char *sw = "abcxyzbaq";
    struct reader s = { sw, sw + 9 };
    printf("switch %d, offset %d\n", switch_walk(&s), (int)(s.pos - sw));

    printf("global %d\n", global_through_pointer("abcdef"));
    printf("local %d\n", local_struct("abcdefghijklmnop", 16));

    const char *words = "hello world";
    struct reader c = { words, words + 11 };
    printf("until space %d, offset %d\n", count_until_space(&c), (int)(c.pos - words));
    return 0;
}
