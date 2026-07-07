/* symex feature test: vassert violation detection — the *_bad suffix
   tells the test runner to expect at least one violated assertion with
   a concrete counterexample. The division-identity assert holds; the
   r > 0 assert is a planted bug (fails whenever y divides x). */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int q, int r){}

int mainQ(int x, int y){
    vassume(x >= 0 && y >= 1);
    int q = 0;
    int r = x;
    while (r >= y) { r = r - y; q = q + 1; }
    vassert(q*y + r == x);   /* holds on every path */
    vassert(r > 0);          /* BUG: violated when y divides x */
    vtrace1(q, r);
    return q;
}
