/* symex feature test: `continue` in a for loop still runs the increment
   (C semantics: continue jumps to `next`, then the guard). Also covers a
   comma expression as `next` and single-statement loop bodies.
   All vasserts must be valid. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int evens, int iters){}

int mainQ(int n){
    vassume(n >= 0 && n <= 5);

    int evens = 0, iters = 0;
    for (int i = 0; i < n; i++) {
        iters++;
        if (i % 2 == 1) continue;   /* i++ must still run */
        evens++;
    }
    vassert(iters == n);
    vassert(evens == (n + 1) / 2);

    int a = 0, b = 10;
    for (int k = 0; k < 3; k++, a++) b--;   /* comma next, one-stmt body */
    vassert(a == 3 && b == 7);

    int m = 0;
    while (m < 2) m++;                      /* one-stmt while body */
    vassert(m == 2);

    vtrace1(evens, iters);
    return evens;
}
