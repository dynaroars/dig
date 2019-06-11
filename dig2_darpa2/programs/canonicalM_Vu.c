#include <stdio.h>
#include <assert.h>

void mainQ(int guess, int t, int n, int secret) {
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
    //%%%traces: int n, int p
}

int main(int argc, char **argv) {
     mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
    return 0;
}
