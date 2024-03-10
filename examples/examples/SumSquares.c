#include <stdio.h>
vassume(int b) {}
vtrace(int n, int sum) {}

int sum_of_squares(int n) {
    int sum = 0;
    for (int i = 1; i <= n; i++) {
        vtrace(n, sum);
        sum += i * i;
    }

    return sum;
    vtrace(n, sum);	
}

int main() {
    mainQ(atoi(argv[1]));
}
