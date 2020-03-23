#include <stdio.h>
#include <assert.h>

int mainQ(int x, int y){
     assert(x>=1);
     assert(y>=1); 

     int a,b,p,q;

     a = x;
     b = y;
     p = 1;
     q = 0;

     while(1) { 
	  //assert(q+a*b*p==x*y);
	  //%%%traces: int x, int y, int a, int b, int p, int q

	  if(!(a!=0 && b!=0)) break;
	  
	  if (a % 2 ==0 && b % 2 ==0 ){
	       a = a/2;
	       b = b/2;
	       p = 4*p;
	  }
	  else if (a % 2 ==1 && b % 2 ==0 ){
	       a = a-1;
	       q = q+b*p;
	  }
	  else if (a % 2 ==0 && b % 2 ==1 ){
	       b = b-1;
	       q = q+a*p;
	  }
	  else {
	       a = a-1;
	       b = b-1;
	       q = q+(a+b+1)*p;  /*dammit I am good ---  was (a+b-1)*/
	  }
     }

     //assert(q == x*y);
     return q; 
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}

