#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int n, int sum, int i){}

void mainQ(int n) {
    if (n >= 1 && n <= 100){
        int sum = 0;
        for (int i = 1; i <= n; i++) {
            sum += i * i;
            vtrace(n, sum, i);
        }
        printf("Sum of squares up to %d is %d\n", n, sum);
    }
}

int main(int argc, char *argv[]) {
        mainQ(atoi(argv[1]));
}
