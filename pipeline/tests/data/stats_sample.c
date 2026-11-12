/* One of every counted kind; the expected counts are in test_stats.py. */
#include <stddef.h>

struct buf {                /* structs */
    char *data;            /* ptr_fields */
    char *pos;             /* ptr_fields */
    size_t len;
    int (*cb)(int);        /* a function pointer: not counted */
};

struct opaque;                       /* a declaration only: not counted in structs */
typedef struct { int x, y; } point;  /* structs (anonymous) */
union value { int i; double d; };    /* unions */

static char *cursor;       /* ptr_globals */
extern char *elsewhere;    /* a declaration, not a definition: not counted */

#define NEXT(p) ((p)++)

int count(const char *s, const char *end, int v[]);    /* a prototype: not counted in functions */

int count(const char *s, const char *end, int v[]) {   /* functions; 3 ptr_params (v is adjusted to a pointer) */
    const char *p = s;                                  /* ptr_locals */
    static int *seen;                                   /* ptr_globals (static storage) */
    int n = 0;
    char arr[4] = "abc";                                /* an array, not a pointer */
    while (p < end) {
        n += p[0] == 'a';                               /* arith_subscript */
        p++;                                            /* arith_move_variable */
    }
    p = p - 1;                                          /* arith_move_variable (not also an offset) */
    n += (int)(end - s);                                /* arith_difference */
    n += *(s + 2);                                      /* arith_offset */
    n += arr[1];                                        /* subscript on an array: not counted */
    NEXT(p);                                            /* arith_move_variable, through a macro */
    (void)seen; (void)v; // p++ in a comment: not counted
    return n + (p != NULL) + (int)sizeof "p++ /* in a string */";
}

void advance(struct buf *b, char **pp) {                /* functions; 2 ptr_params */
    b->pos += 2;                                        /* arith_move_field */
    cursor = cursor + 1;                                /* arith_move_global */
    (*pp)++;                                            /* arith_move_indirect */
}

/* A system-header macro expanding to pointer arithmetic is not the
   project's: isspace is a subscript in glibc's <ctype.h>. */
#include <ctype.h>
int spaces(const char *s) { return isspace(s[0]) != 0; }  /* functions; 1 ptr_params, 1 arith_subscript (s[0]) */
