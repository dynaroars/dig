/* symex feature test: do-while executes its body at least once; break
   exits, continue proceeds to the guard. All vasserts must be valid. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int c, int j){}

int mainQ(int n){
    vassume(n >= 0 && n <= 4);

    int c = 0;
    do { c++; } while (c < n);
    vassert(c == (n < 2 ? 1 : n));   /* runs once even when n == 0 */

    int j = 0, steps = 0;
    do {
        steps++;
        if (steps >= 10) break;          /* safety net, never taken */
        if (j == 2) { j = 5; continue; } /* continue re-tests the guard */
        j++;
    } while (j < 4);
    vassert(j == 5 && steps == 3);

    vtrace1(c, j);
    return c;
}
