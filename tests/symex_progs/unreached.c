/* symex feature test: reachability warnings — vtrace2 sits behind an
   infeasible guard, so unreached_locs() must report it (and the CLI
   prints a warning). The vassert is trivially valid. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int x){}
void vtrace2(int x){}

int mainQ(int x, int y){
    vassert(x == x);
    vtrace1(x);
    if (x > 0 && x < 0) { vtrace2(x); }   /* dead */
    return 0;
}
