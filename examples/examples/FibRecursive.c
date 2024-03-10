#include <stdio.h>
void vassume(int b){}
void vtrace(int n){}

int fib(int n) {
		vtrace(n);
    if (n <= 1) return n;
    return fib(n - 1) + fib(n - 2);
}

int main() {
    int n = 5;
    printf("Fibonacci number at position %d is %d\n", n, fib(n));
    return 0;
}
