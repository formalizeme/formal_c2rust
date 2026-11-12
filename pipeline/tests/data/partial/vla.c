#include "sum.h"

/* A variable-length array: CompCert rejects this file. */
long squares(int n) {
    int a[n];
    for (int i = 0; i < n; i++)
        a[i] = i * i;
    return sum(a, n);
}
