/* symex feature test: k-induction (prove_inductive) — the loop-head
   invariant q*y + r == x is provable for ALL iterations by 1-induction,
   independent of unroll depth; see TestKInduction in test_symex_c.py.
   The vassert here is the bounded version of the same invariant, so the
   program stays self-checking for the generic runner. */
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
        vassert(q*y + r == x);
    }
    vtrace1(q, r);
    return q;
}
