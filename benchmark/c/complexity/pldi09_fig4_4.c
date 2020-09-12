#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace_post(int n, int m, int tCtr, int h){}

int mainQ(int n, int m){
    vassume(m > 0);
    vassume(n > 0);
    vassume(m < 300);
    vassume(n < 300);
    
    int i = n;
    int tCtr = 0;
    int h = n/m;
     
    /* int h = 0; */
    /* while(m*h<=n){ */
    /* 	  h++; */
    /* } */
    /* h--; */
    while(i>0){
	if (i < m) {
	    i--;
	}else{
	    i = i-m;
	}
	tCtr++;
    }

    vtrace_post(n, m, tCtr, h);
     
    /* assert(n%m==0); */

    /* int i = n; */
    /* int t = 0; */
    /* while(i>0){ */
	  
    /* 	  if (i < m) { */
    /* 	       i--; */
    /* 	  }else{ */
    /* 	       i = i-m; */
    /* 	  } */
    /* 	  t++; */
    /* } */
     
     
     
    //%%%traces: int n, int m, int t, int h
     
    //dig2: l26: -c2 <= -1, c2*m - c2 - n + t == 0, c1 - m <= -1, -t <= -2, c1 + c2 - t == 0, c2 - t <= 0

    //Note: I got the above results which I think are right. But I have to manually pass in the flag -maxdeg 3  (i.e., DIG attempts to use maxdeg 4 automatically, but this requires many traces that it wasn't able to get).
     
     
    return 0;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
