#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int v, int safetyBudget, int varUnsafe, int varSafe){}
void vtrace2(int v, int safetyBudget, int varUnsafe, int varSafe){}

int mainQ(int v, int safetyBudget) {
    vassume(1 <= v <= 50);

    vassume(safetyBudget <= 50);



    //int v, safetyBudget;
    //v = VERIFIER_nondet_int();
    //safetyBudget = VERIFIER_nondet_int();

    int varUnsafe, varSafe;
    int iteration = 10;
    while(iteration--) { //////////////////////////////

    while (safetyBudget > 0) {
        safetyBudget = safetyBudget - 1;

        if (v*v + 4*v > 15) {
            safetyBudget = safetyBudget - 4;
            //unsafe
            vtrace1(v, safetyBudget, varUnsafe, varSafe);
        } else {
            //safe
            vtrace2(v, safetyBudget, varUnsafe, varSafe);
        }
    }

    //safe();
    } /////////////////////////
    return 0;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
