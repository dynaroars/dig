/* symex feature test: ternary operator becomes a z3 If expression
   (no path fork). All vasserts must be valid. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int m, int s){}

int mainQ(int x, int y){
    int m = x > y ? x : y;
    vassert(m >= x && m >= y);
    vassert(m == x || m == y);

    int s = x >= 0 ? 1 : -1;
    vassert(s * x >= 0);

    vtrace1(m, s);
    return m;
}
