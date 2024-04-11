#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int n, int sum, int i){}

void mainQ(int n) {
    if (n >= 2 && n <= 100){
        int sum = 0;
        for (int i = 2; i <= n; i += 2) {
            sum += i;
            vtrace(n, sum, i); 
        }
        printf("Sum of even numbers up to %d is %d\n", n, sum);
    }
}

int main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]));
}
