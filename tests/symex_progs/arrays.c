/* symex feature test: 1-D arrays as z3 arrays — {…} initializers with
   zero fill, aliasing-aware store/select, symbolic array parameters,
   the swap idiom, and loops over elements. All vasserts must be valid. */
void vassume(int b){}
void vassert(int b){}
void vtrace1(int s, int e){}

int mainQ(int a[], int i, int j){
    vassume(i != j);

    /* partial initializer: unmentioned elements are 0 */
    int b[4] = {1, 2};
    vassert(b[0] == 1 && b[1] == 2 && b[2] == 0 && b[3] == 0);

    /* stores at distinct symbolic indices don't clobber each other */
    a[i] = 10;
    a[j] = 20;
    vassert(a[i] == 10 && a[j] == 20);

    /* swap */
    int t = a[i];
    a[i] = a[j];
    a[j] = t;
    vassert(a[i] == 20 && a[j] == 10);

    /* element increment statements */
    b[0]++;
    b[1]--;
    vassert(b[0] == 2 && b[1] == 1);

    /* loop over elements */
    int s = 0;
    int k;
    for (k = 0; k < 4; k++) { s = s + b[k]; }
    vassert(s == 3);

    vtrace1(s, a[i]);
    return s;
}
