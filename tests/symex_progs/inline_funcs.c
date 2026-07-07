/* symex feature test: user-defined function inlining — helpers with
   branches (path forks propagate to the caller), loops, and expression
   results. All vasserts must be valid. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int m, int a){}

int imax(int a, int b){ return a > b ? a : b; }

int iabs(int x){
    if (x < 0) { return -x; }
    return x;
}

int sum_to(int n){
    int s = 0;
    int i;
    for (i = 1; i <= n; i++) { s = s + i; }
    return s;
}

int mainQ(int x, int y){
    int m = imax(x, y);
    vassert(m >= x && m >= y);

    int a = iabs(x);
    vassert(a >= 0 && (a == x || a == -x));

    int s = sum_to(3);
    vassert(s == 6);

    vtrace1(m, a);
    return m;
}
