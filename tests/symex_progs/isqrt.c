/* symex feature test: isqrt() is modeled as a fresh symbolic value with
   its defining constraints (s >= 0, s*s <= n < (s+1)^2) instead of
   inlining a loop. All vasserts must be valid. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int s, int n){}

int mainQ(int n, int y){
    vassume(n >= 0);
    int s = isqrt(n);
    vassert(s >= 0 && s*s <= n && (s+1)*(s+1) > n);

    vassume(n == 10);
    vassert(s == 3);

    vtrace1(s, n);
    return s;
}
