#include <stdio.h>
#include <assert.h>


int mainQ(int n) {
     int k = 1;
     int i = 1;
     int j = 0;
     int t = 0;
     while (i <= n - 1) {

	  j = 0;
	  while (j <= i - 1) {
	       k += (i - j);
	       j++;
	       t++;
	  }

	  i++;
     }
     //%%%traces: int n, int k, int i, int j, int t


     assert(k > n - 1);
     return 0;
}

int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}

