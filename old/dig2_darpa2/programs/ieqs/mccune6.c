#include <stdio.h>
#include <assert.h>

void mainQ(int fake){

  int x = 4; int y = 6;
  while (1){
    //−9 <= x − y <= 9
    //−11 <= x + y <= 10
    //−6 <= x <= 6
    //−5 <= y <= 6
       //dig2: y <= 6, -x + y <= 9, -y <= 5, x <= 4, x - y <= 0, -x <= 5, x + y <= 10, -x - y <= 10
    //%%%traces: int x, int y
    
    if (!(x+y >= 0)) break;
    if (y >= 6){x = -x; y = y-1;}
    else{x = x - 1; y = -y;
    }
  }
}

int main(int argc, char **argv){
  mainQ(atoi(argv[1]));
  return 0;
}

