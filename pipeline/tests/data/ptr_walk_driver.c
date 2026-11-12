/* Exercises ptr_walk.c; linked once with the original and once with the
   refactored Clight, the two outputs must be identical. */

#include <stddef.h>
#include <stdio.h>
#include <string.h>

struct cursor { unsigned char *buf; };

unsigned char *fill(unsigned char *out, const unsigned char *src, size_t n);
unsigned next_u32(struct cursor *c);
size_t count_nonzero(const unsigned char *p, const unsigned char *end);
void *copy_bytes(void *dst, const void *src, size_t n);
ptrdiff_t span(const unsigned char *p, const unsigned char *q);

int main(void) {
  unsigned char src[] = {0, 7, 0, 255, 128, 1, 0, 3};
  unsigned char out[16];
  for (size_t n = 0; n <= sizeof src; n++) {
    memset(out, 0xAA, sizeof out);
    unsigned char *r = fill(out, src, n);
    printf("fill n=%zu ret=%td:", n, r - out);
    for (size_t i = 0; i < sizeof out; i++) printf(" %02x", out[i]);
    printf("\n");
  }

  unsigned char buf[] = {0, 0, 1, 2, 0xde, 0xad, 0xbe, 0xef, 0x80, 0, 0, 1};
  struct cursor c = { buf };
  for (int i = 0; i < 3; i++) {
    unsigned v = next_u32(&c);
    printf("next %u at %td\n", v, c.buf - buf);
  }

  for (size_t a = 0; a <= sizeof src; a++)
    for (size_t b = a; b <= sizeof src; b++)
      printf("count [%zu,%zu) = %zu, span = %td\n", a, b,
             count_nonzero(src + a, src + b), span(src + a, src + b));

  for (size_t n = 0; n <= sizeof src; n++) {
    memset(out, 0xAA, sizeof out);
    void *r = copy_bytes(out + 1, src, n);
    printf("copy n=%zu ret=%td:", n, (unsigned char *)r - out);
    for (size_t i = 0; i < sizeof out; i++) printf(" %02x", out[i]);
    printf("\n");
  }
  return 0;
}
