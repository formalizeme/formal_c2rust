#include <stdio.h>
#include "sum.h"

int main(void) {
    int v[] = {5, 4, 3, 2, 1};
    printf("%ld %ld\n", sum(v, 5), squares(10));
    return 0;
}
