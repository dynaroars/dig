#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int n, int sum){}

void mainQ(int n) {
    if (n >= 1 && n <= 100){
        int sum = 0;
        for (int i = 1; i <= n; i++) {
            sum += i * i;
            vtrace(n, sum); 
        }
        printf("Sum of squares up to %d is %d\n", n, sum);
    }
}

int main(int argc, char *argv[]) {
    if (argc == 2) {
        mainQ(atoi(argv[1]));
    } else {
        printf("Usage: %s <n>\n", argv[0]); 
    }
    return 0;
}
