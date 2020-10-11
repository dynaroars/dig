#include <stdio.h>
#include <assert.h>

void mainQ(int Z) {
    int q = 0;

    //assert(Z<3);
    int z=Z;

    int c = 0;
    while (z>0 && c < 3) {
        c++;
        q++;
    }

    while (q > 0 && q <3) {
        q--;
        z = Z;
        c = 0;
        while (z>0 && c < 3) {
            c++;
            q++;
            z--;
        }
        //%%%traces: int q, int Z
    }
}


int main(int argc, char **argv) {
    mainQ(atoi(argv[0]));
    return 0;
}
