//hard: klee timeout

#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work

void mainQ(int ix, int iy){
  int x = ix;
  int y = iy;
  assert (x >= 1);
  assert (y >= 1);

  int r = x;
  while (r >= y){ 
    int b = y;

    while (r >= 2*b){
      //%%%traces: int y
      if (!(y + 9999 >= 0)) {
	printf("input refuting y + 9999 >= 0: %d %d\n", ix, iy);
      }
      if (!(-y + 9999 >= 0)) {
	printf("input refuting -y + 9999 >= 0: %d %d\n", ix, iy);
      }
      
      b = 2*b;
    }

    r = r - b;
  }

  
  /* if (x + y >= 7){ */
  /*   //%%%traces: int x, int y */
  /* } */


  /* if(0){ */
  /*   //%%%traces: int x, int y */
  /* } */
}

int main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}

