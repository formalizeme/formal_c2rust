/* Test input for ptridxgen: the pointer-arithmetic shapes from amp
   (pointer_arithmetic_refactor.md §10), without amp's variable-length array. */

#include <stddef.h>

struct cursor { unsigned char *buf; };

/* A parameter that never moves: already base + constant index. */
static unsigned read_u32_be(const unsigned char *p) {
  return (unsigned)p[0] << 24 | (unsigned)p[1] << 16 | (unsigned)p[2] << 8 | p[3];
}

/* A moving pointer temporary with copies, like amp_encode's buf and ret. */
unsigned char *fill(unsigned char *out, const unsigned char *src, size_t n) {
  unsigned char *start = out;
  *out++ = (unsigned char)n;
  for (size_t i = 0; i < n; i++)
    *out++ = src[i];
  return start;
}

/* A pointer stored in memory and advanced, like amp_decode_arg's msg->buf. */
unsigned next_u32(struct cursor *c) {
  unsigned v = read_u32_be(c->buf);
  c->buf += 4;
  return v;
}

/* Comparison within one buffer. */
size_t count_nonzero(const unsigned char *p, const unsigned char *end) {
  size_t k = 0;
  for (; p < end; p++)
    if (*p) k++;
  return k;
}

/* A void * copied into a char * that moves, like memcpy: only the char *
   is split (arithmetic on void * would be rejected by CompCert's backend). */
void *copy_bytes(void *dst, const void *src, size_t n) {
  unsigned char *d = dst;
  const unsigned char *s = src;
  while (n--)
    *d++ = *s++;
  return dst;
}

/* Difference within one buffer. */
ptrdiff_t span(const unsigned char *p, const unsigned char *q) {
  return q - p;
}
