#include <stdio.h>
#include <assert.h>

int mainQ(int m){

     int x = 0;
     int y = 0;
     int t = 0;
     while(x < 100 && y < m){
	  y++;
	  t++;
     }
     while(x < 100 && y >= m){
	  x++;
	  t++;
     }

     //%%%traces: int m, int t
     //dig2: m*t - (t*t) - 100*m + 200*t - 10000 == 0
     //solve for t: t == m + 100, t == 100
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}
