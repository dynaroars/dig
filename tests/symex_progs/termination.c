/* symex feature test: termination proving — the loop terminates because
   r decreases by at least y >= 1 every iteration and is bounded below
   while iterating. Proved unboundedly via
     prove_termination(rank=r, assume=[y >= 1])
   (CLI: --terminates "r" --assume "y >= 1"; the assume is itself
   verified inductive first). The vasserts keep it self-checking. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int q, int r){}

int mainQ(int x, int y){
    vassume(x >= 0 && y >= 1);
    int q = 0;
    int r = x;
    while (r >= y) {
        r = r - y;
        q = q + 1;
        vassert(r >= 0);
    }
    vtrace1(q, r);
    return q;
}
