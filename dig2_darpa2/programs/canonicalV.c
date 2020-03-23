#include <stdio.h>
#include <assert.h>

void mainQ(int guess, int t, int n, int m, int d, int secret) {
     assert(0<=t <= 2);
     
    int p = 0;
    int i = 0;
    if(guess <= secret){
        if(t == 1){
            p += 1;
        }
        else if(t == 2){
            for(i = 0; i<n;i++){
                p += 1;
            }
        }
        else{
            for(i = 0; i<d;i++){
                p += 1;
            }
        }
    }
    else{
        if(t == 1){
            p += 1;
        }
        else if(t == 2){
            for(i = 0; i<m;i++){
                p += 1;
            }
        }
        else{
            for(i = 0; i<d;i++){
                p += 1;
            }
        }
    }
    //%%%traces: int n, int t, int p, int m, int d
}

int main(int argc, char **argv) {
    mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]), atoi(argv[6]));
    return 0;
}
