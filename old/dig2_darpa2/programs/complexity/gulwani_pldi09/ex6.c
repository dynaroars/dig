#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work
#include <time.h>


int mainQ(int n, int m){
     assert (0 <= n);
     assert (0 <= m);
     int i = 0;
     int j = 0;
     int k = 0;
     int t = 0;

     while(i++ < n){
	  //note remove if(nondet)
	  t++;
	  if (i % 2){//odd
	       while(j++ < m){t++;}
	  }
	  else{
	       while(k++ < m){t++;}
	  }
     }
     //%%%traces: int n, int m, int i, int t
     //dig2: i - n - 1 == 0, -m - t <= 0, 2*m*n - n*t == 0, 2*m*t - (t*t) == 0, -i <= -1
     //NOTE: *** these equalities don't seem to capture the correct bound n+2m ? ***
     //Timos: This is because we haven't added a t++ for the outer loop. I suspect once we do that we will get what we want.
     return 0;
}


int main(int argc, char **argv){
     srand(time(NULL));
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
