#include <stdio.h>
#include <assert.h>

int mainQ(int n, int m){
     assert(m>=0); 
     int x = 0;
     int y = 0;
     int t = 0;
     while(x < n){
	  if(y < m){
	       y = y + 1;
	  }
	  else{
	       x = x + 1;
	  }
	  t++;
     }
     //%%%traces: int n, int m, int t
     //dig2:n - t <= 0, -t <= 0    nothing useful ??
     //NOTE: should we expect t = something here ? 
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
