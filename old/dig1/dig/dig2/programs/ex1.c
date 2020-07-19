#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work

void mainQ(int xinp){
  assert (xinp >= 10);
  int x = xinp + 2;
  
  while (1){
    //%%%traces: int x
    //%%%traces: int xinp
    
    if (!(x <= 100))break;
    x = x + 1;
  }
}

int main(int argc, char **argv){
  mainQ(atoi(argv[1]));
  return 0;
}

