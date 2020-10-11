#include <stdio.h>
#include <assert.h>

void mainQ(int fake){

  int x = 2 ; int y = 3 ;
  while (1){
       //-5  <= x + y <= 7

       //dig2: -x - y <= 5, -x + y <= 15, y <= 5, x + y <= 7, -x <= 10, x <= 7, x - y <= 7, -y <= 0
       //%%%traces: int x, int y      
       if (!(x+y >= 0)){
	    break;
       }
       
       if (y >= 2) {
	    y = -y + 4;
	    x = -x + 3;
       }
       else{
	    x = -x-3;
	    y = -y+5;
       }
  }
}

int main(int argc, char **argv){
  mainQ(atoi(argv[1]));
  return 0;
}

