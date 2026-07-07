/* symex feature test: unknown()/nondet() are fresh, independent symbolic
   values — usable in declarations, assignments, and conditions.
   All vasserts must be valid. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int lo, int x){}
int unknown(void);

int mainQ(int x, int y){
    int u = unknown();
    int w = unknown();
    int lo = u < w ? u : w;
    vassert(lo <= u && lo <= w);

    if (unknown()) { x = 1; } else { x = 2; }
    vassert(x == 1 || x == 2);

    vtrace1(lo, x);
    return 0;
}
