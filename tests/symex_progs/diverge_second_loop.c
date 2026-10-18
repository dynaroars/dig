/* symex feature test: prove_any_nontermination() must not stop at loop #0.
   The first loop terminates, so the witness has to come from the second,
   which runs forever for every x > 0 — reported as loop #1 with a concrete
   diverging input. The vasserts self-check the paths that do reach the
   trace, i.e. those entering with x <= 0. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int x, int y){}

int mainQ(int x, int y){
    int c = 0;
    while (c < 2) { c = c + 1; }
    while (x > 0) { y = 1 - y; }
    vtrace1(x, y);
    vassert(c == 2);
    vassert(x <= 0);
    return y;
}
