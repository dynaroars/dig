#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace_post(int n, int m, int y, int x, int tCtr){}

int mainQ(int n, int m){
    vassume(m >= 0);
    vassume(n >= 0);
    int x = 0;
    int y = 0;
    int tCtr = 0;
    while(x < n){
	if(y < m){
	    y++;
	}
	else{
	    y=0;
	    x++;
	}
	tCtr++;
    }

    vtrace_post(n, m, y, x, tCtr);

    //%%%traces: int n, int m, int y, int x, int t
    //dig2:  y <= 0, -x <= 0, n - t <= 0, -t + x <= 0, n*t - t*x == 0, -y <= 0
    //NOTE: *** does this eq  n*t - t*x == 0  give us anything useful about the complexity?  ***
    //Timos: I tried this example with DIG1 and I got m*n + n - t == 0 which looks exactly right. Is there something missing above?
    //Timos: UPDATE: With the vassume statements above, the correct bound is given, although if we leave the variable x in the traces, we get this:
    //m*x - t + x == 0, n - x == 0, y == 0, which implies m*n - t + n == 0
    return 0;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
