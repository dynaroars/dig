#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(void) { 
  int i = 0;
  int c = 0;

  while (i < 1000) {
    c = c + i;
    i = i + 1;
  }

  //%%%traces: int c, int i
  //assert(c >= 0);
}

int main(int argc, char *argv[]) {
  mainQ();
  return 0;
} 
