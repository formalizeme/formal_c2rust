#include "sum.h"

long sum(const int *p, int n) {
    long s = 0;
    const int *end = p + n;
    while (p < end)
        s += *p++;
    return s;
}
