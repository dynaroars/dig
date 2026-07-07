/* symex feature test: C division semantics — "/" and "%" truncate toward
   zero and the remainder takes the dividend's sign (z3's own Int division
   is Euclidean and disagrees on negatives). All vasserts must be valid. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int q, int r){}

int mainQ(int x, int y){
    vassume(y >= 1);

    int q = x / y;
    int r = x % y;
    vassert(q*y + r == x);                              /* identity, any sign */
    vassert((x >= 0 && r >= 0) || (x <= 0 && r <= 0));  /* remainder sign */

    /* concrete C99 checks, all four sign combinations */
    vassert(7 / 2 == 3 && 7 % 2 == 1);
    vassert(-7 / 2 == -3 && -7 % 2 == -1);
    vassert(7 / -2 == -3 && 7 % -2 == 1);
    vassert(-7 / -2 == 3 && -7 % -2 == -1);

    vtrace1(q, r);
    return q;
}
