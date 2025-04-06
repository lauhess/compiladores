#include <stdio.h>
#include <stdlib.h> /* atoi() */
#include <assert.h>

// Directly from definition
unsigned int naive_ackermann(unsigned int m, unsigned int n) {
    if (m == 0)
        return n + 1;
    else if (n == 0)
        return naive_ackermann(m - 1, 1);
    else
        return naive_ackermann(m - 1, naive_ackermann(m, n - 1));
}

int main(int argc, char* argv[]) {
    int result = naive_ackermann(3, 8);
    printf("ack 3 8 = %d\n", result);
    return 0;
}
