#include <stdio.h>
#include <assert.h>

void mainQ(int guess, int t, int n, int m, int d, int secret) {
    int p = 0;
    int i = 0;
    assert(guess <= secret);
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
            for(i = 0; i<n*n*n;i++){
                p += 1;
            }
        }
    }
    else{
        if(t == 1){
            p += 1;
        }
        else if(t == 2){
            for(i = 0; i<n*n;i++){
                p += 1;
            }
        }
        else{
            for(i = 0; i<n*n*n;i++){
                p += 1;
            }
        }
    }


    int n2 = n*n;
    int n3 = n*n*n;
    //%%%traces: int secret, int p, int n, int n2, int n3
}

int main(int argc, char **argv) {
    mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]), atoi(argv[6]));
    return 0;
}
