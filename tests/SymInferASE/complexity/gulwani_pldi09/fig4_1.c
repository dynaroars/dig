#include <stdio.h>
#include <assert.h>


int mainQ(int id, int n){
     assert (id >= 0);
     assert (n > id);
     int tmp = id + 1;
     int t = 0;

     while(tmp != id){
	  if (tmp <= n) {
	       tmp = tmp + 1;
	  }else{
	       tmp=0;
	  }
	  t++;
     }
     //%%%traces: int id, int n, int t
     //dig2: n - t + 1 == 0, -id <= 0, id - n <= -1 
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
