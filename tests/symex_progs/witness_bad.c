/* symex feature test: witness traces — the violation is only reachable
   down one specific branch sequence (x > 0, then the y > x else-branch,
   with x == y), and the reported AssertResult.trace must show exactly
   those decisions with source locations. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int a, int x){}

int mainQ(int x, int y){
    vassume(y >= 0);
    int a = 0;
    if (x > 0) {
        if (y > x) { a = y - x; } else { a = x - y; }
        vassert(a > 0);      /* BUG: a == 0 when x == y */
    }
    vtrace1(a, x);
    return a;
}
