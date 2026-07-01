#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int v, int safetyBudget, int varUnsafe, int varSafe){}
void vtrace2(int v){}

int mainQ(int v, int safetyBudget) {
    int varUnsafe, varSafe;
    int a;

    while (safetyBudget > 0) {
        a = rand()%4 - 2;

        v = v + a;

        if (v*v + v > 15) {
            safetyBudget = safetyBudget - 4;
            // unsafe
            //vtrace1(v, safetyBudget, varUnsafe, varSafe);
            varUnsafe = 1;
            varSafe = 0;
        } else {
            vtrace2(v);
            if (safetyBudget < 20)
                safetyBudget = safetyBudget + 1;
            // safe
            varUnsafe = 0;
            varSafe = 1;
            
        }
    }

    return 0;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

