/* Calls every function of mem_walk.c and prints what they compute. */
#include <stdio.h>
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

int count_lines(struct reader *r);
unsigned sum_bytes(struct reader *r, int n);
char *take_string(struct reader *r);
void put_char(struct writer *w, char c);
void put_string(struct writer *w, const char *s);
void set_cursor(const char *s);
int skip_spaces(void);
int next_int(const int **pp);
int total(struct reader *rs, int k);
int rewind_and_count(struct reader *r, const unsigned char *start);

static const unsigned char text[] = "one\ntwo\nthree\n";

int main(void) {
    struct reader r = { text, text + sizeof text - 1, 0 };
    printf("lines %d, at end %d\n", count_lines(&r), r.pos == r.end);

    r.pos = text;
    printf("sum %u, offset %d\n", sum_bytes(&r, 5), (int)(r.pos - text));
    printf("sum %u, offset %d\n", sum_bytes(&r, 100), (int)(r.pos - text));

    unsigned char msg[] = { 0, 0, 0, 5, 'h', 'e', 'l', 'l', 'o', 0, 0, 0, 2, 'h', 'i' };
    struct reader m = { msg, msg + sizeof msg, 0 };
    char *a = take_string(&m);
    char *b = take_string(&m);
    printf("%s %s, offset %d\n", a, b, (int)(m.pos - msg));
    free(a);
    free(b);

    char buf[32];
    struct writer w = { buf, 0 };
    put_char(&w, '[');
    put_string(&w, "pointer");
    put_char(&w, ']');
    *w.out = 0;
    printf("%s, %zu put_char calls, %d written\n", buf, w.written, (int)(w.out - buf));

    set_cursor("   x  y");
    printf("spaces %d", skip_spaces());
    printf(" %d\n", skip_spaces());

    int nums[] = { 7, 8, 9 };
    const int *p = nums;
    int s = next_int(&p);
    s = s * 10 + next_int(&p);
    printf("next %d, offset %d\n", s, (int)(p - nums));

    struct reader rs[3] = {
        { text, text + 3, 0 }, { text + 4, text + 7, 0 }, { text, text, 0 },
    };
    printf("total %d, offsets %d %d %d\n", total(rs, 3),
           (int)(rs[0].pos - text), (int)(rs[1].pos - text), (int)(rs[2].pos - text));

    struct reader q = { NULL, text + 9, 0 };
    printf("rewind %d, offset %d\n", rewind_and_count(&q, text), (int)(q.pos - text));
    return 0;
}
