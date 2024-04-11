#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void mainQ(int MAXPATHLEN, int u) {
  assert(MAXPATHLEN > 0);

  int buf_off = 0;
  int pattern_off = 0;

  int bound_off = 0 + (MAXPATHLEN + 1) - 1;

  int glob3_pathbuf_off = buf_off;
  int glob3_pathend_off = buf_off;
  int glob3_pathlim_off = bound_off;
  int glob3_pattern_off = pattern_off;

  int glob3_dc = 0;
  int flag = 0;

  if (glob3_pathend_off + glob3_dc >= glob3_pathlim_off)
    flag = 0;
  else
    flag = 1;
  while (flag != 0) {

    glob3_dc++;
    //%%%traces: int glob3_dc, int MAXPATHLEN
    //assert(0 <= glob3_dc);
    //assert(glob3_dc < MAXPATHLEN + 1);

    if (u)
      flag = 0;
    else if (glob3_pathend_off + glob3_dc >= glob3_pathlim_off)
      flag = 0;
    else
      flag = 1;
  }
}

int main(int argc, char *argv[]) {
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}
