#include <stdio.h>
#include <stdlib.h>  //required for afloat to work

void vassume(int b){}
void vtrace_post(int n, int m, int i, int tCtr){}

int mainQ(int n, int m){
    vassume (0 <= n);
    vassume (0 <= m);
    /* vassume (n <= 10); */
    /* vassume (m <= 10); */
    
    int i = 0;
    int j = 0;
    int k = 0;
    int tCtr = 0;

    while(i++ < n){
	//note remove if(nondet)
	tCtr++;
	if (i % 2){//odd
	    while(j++ < m){tCtr++;}
	}
	else{
	    while(k++ < m){tCtr++;}
	}
    }
    //%%%traces: int n, int m, int i, int t
    //dig2: i - n - 1 == 0, -m - t <= 0, 2*m*n - n*t == 0, 2*m*t - (t*t) == 0, -i <= -1
    //NOTE: *** these equalities don't seem to capture the correct bound n+2m ? ***
    //Timos: This is because we haven't added a t++ for the outer loop. I suspect once we do that we will get what we want.
    vtrace_post(n, m, i, tCtr);
    return 0;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
