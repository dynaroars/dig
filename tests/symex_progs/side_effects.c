/* symex feature test: side effects in conditions and pre/post increment
   value semantics. The loop condition i++ < n is evaluated n+1 times
   (including the final failing test), so i == n+1 on exit.
   All vasserts must be valid. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int i, int j){}

int mainQ(int n, int y){
    vassume(n >= 0 && n <= 3);

    int i = 0;
    while (i++ < n) { }
    vassert(i == n + 1);

    int j = 5;
    int a = ++j;        /* pre: yields the new value */
    int b = j++;        /* post: yields the old value */
    vassert(a == 6 && b == 6 && j == 7);

    int x = 1;
    if (x-- > 0) { vassert(x == 0); }   /* decrement applies in both branches */

    vtrace1(i, j);
    return i;
}
