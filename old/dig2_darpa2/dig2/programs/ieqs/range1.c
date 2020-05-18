#include <stdio.h>
#include <assert.h>


void mainQ(int x){
     assert (x <= 6);
     //%%%traces: int x
}

int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
  return 0;
}

