#include <stdio.h>
#include <assert.h>

void mainQ(int fake){

  int x = 10 ; int y = 0 ;
  while (1){
    //2 <= x - y <= 10 
    //x + y <= 10 
    //4 <= x <= 10 
    //0 <= y <= 2
    //Dig2 x - y <= 10, y <= 2, x <= 10, -x - y <= -4, -x + y <= -2, x + y <= 10, -x <= -4, -y <= 0
    //Dig2 -x - y <= -4, y <= 2, x + y <= 10, x <= 10, -x + y <= -2, x - y <= 10, -x <= -4, -y <= 0
	    
	    
    //%%%traces: int x, int y      
    if (!(x-y >= 3)){
      break;
    }
    
    if (x >= 5) x = x-1;
    else y = y+1;
    
  }
}

int main(int argc, char **argv){
  mainQ(atoi(argv[1]));
  return 0;
}

