/* symex feature test: C truthiness — integer expressions as conditions
   (if (x % 2), while (n), !y, x && y) mean expr != 0.
   All vasserts must be valid. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int c, int n){}

int mainQ(int x, int y){
    vassume(x == 6 && y == 0);

    int odd = 0;
    if (x % 2) { odd = 1; }
    vassert(odd == 0);              /* 6 is even */

    if (!y) { odd = 2; }            /* !0 is true */
    vassert(odd == 2);

    int n = 3;
    int c = 0;
    while (n) { n = n - 1; c = c + 1; }
    vassert(c == 3 && n == 0);

    vassert(x && !y);               /* 6 && !0 */

    vtrace1(c, n);
    return 0;
}
