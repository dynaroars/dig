#include <stdio.h>
#include <assert.h>


void mainQ(int x, int y){
     assert (10 <= x - y);
     assert (x - y <= 199);
     //%%%traces: int x, int y

}

int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}

