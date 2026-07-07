/* symex feature test: auto array-bounds check (check_safety) — the
   declared size of a[] is 4, but the vassume allows i >= 4, so the
   engine must report an out-of-bounds access with a concrete i. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int v){}

int mainQ(int i, int y){
    vassume(i >= 0);           /* i < 4 NOT guaranteed */
    int a[4] = {1, 2, 3, 4};
    int v = a[i];              /* BUG: out of bounds when i >= 4 */
    vtrace1(v);
    return v;
}
